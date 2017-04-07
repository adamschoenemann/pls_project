Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

Module FingerTrees.

  Import List.ListNotations.

  Open Scope list_scope.

  Class monoid A := Monoid {
    id: A;
    mappend: A -> A -> A;

    mappendAssoc : forall x y z, mappend x (mappend y z) = mappend (mappend x y) z;
    idL: forall x, mappend id x = x;
    idR: forall x, mappend x id = x;
  }.

  Instance nat_plus_monoid : monoid nat :=
    {|
      id := 0;
      mappend := plus;

      mappendAssoc := plus_assoc;
      idL := plus_O_n;
      idR := fun n => eq_sym (plus_n_O n);
    |}.

  Class reduce F := Reduce {
    reducer : forall {A} {B}, (A -> B -> B) -> (F A -> B -> B);
    reducel : forall {A} {B}, (B -> A -> B) -> (B -> F A -> B);
  }.

  Search "fold".
  Instance list_reduce : reduce list :=
    {|
      reducer := fun _ _ fn xs z => List.fold_right fn z xs;
      reducel := fun _ _ fn z xs => List.fold_left fn xs z;
    |}.

  Definition to_list {F: Type -> Type} {r: reduce F} {A : Type} (s : F A) : list A :=
    reducer (cons (A:=A)) s nil.

  Inductive node (A:Type) : Type :=
  | node2: A -> A -> node A
  | node3: A -> A -> A -> node A.

  Arguments node2 {A} _ _.
  Arguments node3 {A} _ _ _.
  
  Inductive tree (A:Type) : Type :=
  | zero : A -> tree A
  | succ : tree (node A) -> tree A.

  Arguments zero {A} _.
  Arguments succ {A} _.

  Inductive digit (A:Type) : Type :=
  | one : A -> digit A
  | two : A -> A -> digit A
  | three : A -> A -> A -> digit A
  | four : A -> A -> A -> A -> digit A.

  Arguments one {A} _.
  Arguments two {A} _ _.
  Arguments three {A} _ _ _.
  Arguments four {A} _ _ _ _.

  Inductive fingertree (A:Type) : Type := 
  | empty : fingertree A
  | single : A -> fingertree A
  | deep : digit A -> fingertree (node A) -> digit A -> fingertree A.

  Arguments empty {A}.
  Arguments single {A} _.
  Arguments deep {A} _ _ _.

  Instance node_reduce : reduce node :=
    {|
      reducer := fun _ _ op nd z => match nd with
                                  | node2 a b => op a (op b z)
                                  | node3 a b c => op a (op b (op c z))
                                  end;
      reducel := fun _ _ op z nd => match nd with
                                  | node2 a b => op (op z b) a
                                  | node3 a b c => op (op (op z c) b) a
                                  end;
      |}.

  Definition digit_reducer {A B : Type} (op: A -> B -> B) dg z := 
    match dg with
    | one a => op a z
    | two a b => op a (op b z)
    | three a b c => op a (op b (op c z))
    | four a b c d => op a (op b (op c (op d z)))
    end.

  Definition digit_reducel {A B : Type} (op: B -> A -> B) z dg :=
    match dg with
    | one a => op z a
    | two a b => op (op z a) b
    | three a b c => op (op (op z a) b) c
    | four a b c d => op (op (op (op z a) b) c) d
    end.

  Instance digit_reduce : reduce digit :=
    {|
      reducer := fun A B op dg z => @digit_reducer A B op dg z;
      reducel := fun A B op z dg => @digit_reducel A B op z dg;
    |}.

  Fixpoint fingertree_reducer {A:Type} {B:Type}
             (op: A -> B -> B) (tr : fingertree A) (z : B) : B :=
      match tr with
      | empty => z
      | single x => op x z
      | deep pr m sf =>
        let op' := reducer op in
        let op'' := fingertree_reducer (reducer op) in
        op' pr (op'' m (op' sf z))
      end.

  Fixpoint fingertree_reducel {A:Type} {B:Type}
           (op: B -> A -> B) (z : B) (tr : fingertree A) : B :=
      match tr with
      | empty => z
      | single x => op z x
      | deep pr m sf =>
        let op'  := reducel op in
        let op'' := fingertree_reducel (reducel op) in
        op' (op'' (op' z pr) m) sf
      end.

  Instance fingertree_reduce : reduce fingertree :=
    {|
      reducer := @fingertree_reducer;
      reducel := @fingertree_reducel;
    |}.

  Fixpoint addl {A:Type} (a:A) (tr:fingertree A) : fingertree A  :=
    match tr with
    | empty => single a
    | single b => deep (one a) empty (one b)
    | deep (four b c d e) m sf => deep (two a b) (addl (node3 c d e) m) sf
    | deep (three b c d) m sf => deep (four a b c d) m sf
    | deep (two b c) m sf => deep (three a b c) m sf
    | deep (one b) m sf => deep (two a b) m sf
    end.


  Fixpoint addr {A:Type} (tr:fingertree A) (a:A) : fingertree A  :=
    match tr with
    | empty => single a
    | single b => deep (one b) empty (one a)
    | deep pr m (four e d c b) => deep pr (addr m (node3 e d c)) (two b a)
    | deep pr m (three e c b) => deep pr m (four e c b a)
    | deep pr m (two c b) => deep pr m (three c b a)
    | deep pr m (one b) => deep pr m (two b a)
    end.

  Notation "x <| t" := (addl x t)
                     (at level 60, right associativity).
  Notation "x |> t" := (addr x t)
                     (at level 61, left associativity).

  Definition addl' {F: Type -> Type} {r:reduce F} {A:Type} :
    F A -> fingertree A -> fingertree A :=
      reducer addl.

  Definition addr' {F: Type -> Type} {r:reduce F} {A:Type} :
    fingertree A -> F A -> fingertree A :=
      reducel addr.

  Definition to_tree {F:Type -> Type} {A:Type} {r:reduce F} (s:F A) :
    fingertree A := addl' s empty.

  Inductive View_l (S:Type -> Type) (A:Type): Type :=
  | nil_l : View_l S A
  | cons_l : A -> S A -> View_l S A.

  Arguments nil_l {S} {A}.
  Arguments cons_l {S} {A} _ _.

  Fixpoint to_digit {A:Type} (nd:node A) : digit A :=
    match nd with
    | node2 a b => two a b
    | node3 a b c => three a b c
    end.

  Fixpoint view_l {A:Type} (tr:fingertree A) : View_l fingertree A :=
    match tr with
    | empty => nil_l
    | single x => cons_l x empty
    | deep (one x) m sf =>
      let tail := match view_l m with
                  | nil_l => to_tree sf
                  | cons_l a m' => deep (to_digit a) m' sf
                  end
      in cons_l x tail
    | deep (two x y) m sf => cons_l x (deep (one x) m sf)
    | deep (three x y z) m sf => cons_l x (deep (two x y) m sf)
    | deep (four x y z u) m sf => cons_l x (deep (three x y u) m sf)
    end.

  Definition is_emptyb {A:Type} (tr:fingertree A) : bool :=
    match view_l tr with
    | nil_l => true
    | cons_l _ _ => false
    end.

  Definition is_empty {A:Type} (tr:fingertree A) : Prop :=
    match view_l tr with
    | nil_l => True
    | cons_l _ _ => False
    end.

  Lemma view_l_nil_empty : forall {A : Type} tr, @view_l A tr = nil_l <-> tr = empty.
  Proof.
    intros. split.
    - intros. destruct tr; [reflexivity | inversion H |]. simpl in H.
      destruct d, (view_l tr), d0; inversion H.
    - intros. destruct tr; [reflexivity | inversion H |].
      destruct d, (view_l tr), d0; inversion H.
  Qed.

  Lemma to_tree_empty : forall (A : Type), @is_empty A (to_tree []).
  Proof.
    intros. simpl. unfold is_empty. destruct (view_l empty) eqn:Heq.
    - apply I.
    - inversion Heq.
  Qed.

  Lemma addl_not_empty : forall (A : Type) (tr : fingertree A) x, ~(addl x tr = empty).
  Proof.
    intros A tr x H. induction tr; inversion H.
    destruct d; inversion H1.
  Qed.

  Lemma addl_not_2single : forall (A : Type) (x y z : A), ~(addl x (single y) = single z).
  Proof.
    intros A x y z H. simpl in H. inversion H.
  Qed.

  Lemma addr_not_empty : forall (A : Type) (tr : fingertree A) x, ~(addr tr x = empty).
    intros A tr x H. induction tr; inversion H.
    destruct d0; inversion H1.
  Qed.

  (* should reuse lemmas from above, but cant figure out how right now
     (in my defense, I am a bit drunk)
  *)
  Lemma addl_not_nil : forall (A : Type) (tr : fingertree A) x,
      ~(view_l (addl x tr) = nil_l).
  Proof.
    intros A tr x H. induction tr; inversion H.
    destruct d; inversion H1.
  Qed.

  Definition head_l {A:Type} (a:A) (tr:fingertree A) : A :=
    match view_l tr with
    | nil_l => a
    | cons_l x _ => x
    end.

  Definition tail_l {A:Type} (tr:fingertree A) : fingertree A :=
    match view_l tr with
    | nil_l => tr
    | cons_l _ tl => tl
    end.

  Lemma fold_right_empty : forall {A : Type} (xs : list A),
      fold_right addl empty xs = empty -> xs = [].
  Proof.
    induction xs.
    - intros. reflexivity.
    - intros. simpl in H. exfalso. eapply addl_not_empty. apply H.
  Qed.

  Lemma fold_right_single : forall {A : Type} (xs : list A) x,
      fold_right addl empty xs = single x -> xs = [x].
  Proof.
    induction xs; [intros; inversion H|].
    intros. simpl in H. destruct (fold_right addl empty xs) eqn:Heq.
    - simpl in *. inversion H. rewrite (fold_right_empty _ Heq). reflexivity.
    - exfalso. apply (addl_not_2single _ a a0 x H).
    - simpl in H. destruct d; inversion H.
  Qed.

  (* if you add an x to the left of a tree tr and then convert it to a list, it is
     the same as converting tr to a list and then consing x
  *)
  Lemma ft_reducer_addl : forall {A : Type}  {F : Type -> Type}
                         (tr : fingertree (F A)) xs x
                         (op : F A -> list A -> list A),
      fingertree_reducer op (x <| tr) xs = op x (fingertree_reducer op tr xs).
  Proof.
    intros A F tr.
    induction tr; intros; try reflexivity.
    destruct d; try reflexivity.  simpl.
    do 2 (apply f_equal). 
    remember (fun (nd : node A0) (z : list A) =>
                match nd with
                | node2 a3 b => op a3 (op b z)
                | node3 a3 b c => op a3 (op b (op c z))
                end) as l.
    specialize (IHtr (digit_reducer op d0 xs) (node3 a0 a1 a2) l).
    rewrite IHtr. rewrite Heql. reflexivity.
  Qed.

  (* Lemma ft_reducer_app_r : forall {A : Type} {F : Type -> Type} *)
  (*                            (tr : fingertree (F A)) xs x *)
  (*                            (op : list A -> F A -> list A), *)
  (*     fingertree_reducer op (tr |> x) xs = op xs  *)


  Theorem to_tree_to_list_id : forall {A:Type} (xs : list A),
      to_list (to_tree xs) = xs.
  Proof.
    intros. induction xs.
    - reflexivity.
    - simpl. rewrite @ft_reducer_addl with (op := cons) (F := fun x => x).
      apply f_equal. simpl in IHxs. assumption.
  Qed.

  (* Adam *)

  Fixpoint dig_app3 {A:Type} (ds1 : digit A) (ds2 : list A) (ds3 : digit A): list A :=
    to_list ds1 ++ ds2 ++ to_list ds3.

  Fixpoint nodes {A : Type} (xs : list A) : list (node A) :=
    match xs with
    | [] => [] (* should never happen *)
    | [x] => [] (* should never happen *)
    | [a;b] => [node2 a b]
    | [a;b;c] => [node3 a b c]
    | a :: b :: c :: xs' => node3 a b c :: nodes xs'
    end.

  Fixpoint app3 {A:Type} (tr1:fingertree A) (ds:list A) (tr2:fingertree A)
    : fingertree A :=
    match tr1, tr2 with
    | empty, _ => addl' ds tr2
    | _, empty => addr' tr1 ds
    | single x, _ => x <| addl' ds tr2
    | _, single x => addr' tr1 ds |> x
    | deep pr1 m1 sf1, deep pr2 m2 sf2 =>
        deep pr1 (app3 m1 (nodes (dig_app3 sf1 ds pr2)) m2) sf2
    end.


  Fixpoint append {A:Type}
           (tr1 : fingertree A) (tr2 : fingertree A) : fingertree A :=
    app3 tr1 [] tr2.

  
  Notation "t1 >< t2" := (append t1 t2)
                     (at level 62, left associativity).

  Theorem digit_reducer_app :
    forall {A B : Type} (xs ys : list A) d (op : B -> list A -> list A),
      (forall a xs ys, op a (xs ++ ys) = (op a xs) ++ ys) ->
      (digit_reducer op d (xs ++ ys) = digit_reducer op d xs ++ ys).
  Proof.
    intros.
    destruct d; simpl; rewrite ?H; reflexivity.
  Qed.

  Theorem ft_reducer_app :
    forall {A : Type} {F : Type -> Type}
      (tr : fingertree (F A)) (xs ys : list A)
      (op : F A -> list A -> list A),
      (forall a (xs ys : list A), op a (xs ++ ys) = (op a xs) ++ ys) ->
      fingertree_reducer op tr (xs ++ ys) = (fingertree_reducer op tr xs) ++ ys.
  Proof.
    intros A F tr. induction tr; intros; [reflexivity | apply H |].
    simpl.
    remember (fun (nd : node A0) (z : list A) =>
      match nd with
      | node2 a1 b => op a1 (op b z)
      | node3 a1 b c => op a1 (op b (op c z))
      end) as f.
    assert (forall (a1 : node A0) (xs0 ys0 : list A), f a1 (xs0 ++ ys0) = f a1 xs0 ++ ys0).
    - intros. rewrite Heqf. destruct a1; rewrite ?H; reflexivity.
    - rewrite (digit_reducer_app xs ys d0 op H).
      rewrite (IHtr _ _ f H0).
      remember (fingertree_reducer f tr (digit_reducer op d0 xs)) as xs'.
      apply (digit_reducer_app xs' ys d op H).
  Qed.

  Lemma app_cons : forall {A : Type} (x : A) xs, x :: xs = [x] ++ xs.
  Proof.
    intros. reflexivity.
  Qed.

  Fixpoint last_safe {A : Type} (l : list A) (p:l <> []) {struct l} : A.
  Proof.
    destruct l as [| x l'].
    - contradiction p. reflexivity.
    - destruct l' as [| y l''] eqn:Hl'.
      + apply x.
      + apply (last_safe A (l')). intros H. subst. inversion H.
  Qed.

  Fixpoint init_safe {A : Type} (l : list A) (p:l <> []) {struct l} : list A.
  Proof.
    destruct l as [| x xs].
    - contradiction p. reflexivity.
    - destruct xs as [| x' xs'] eqn:Hxs.
      + apply [].
      + assert (xs <> []). intros H. subst. inversion H.
        apply (x :: init_safe A xs H).
  Qed.

  Lemma init_last : forall { A : Type} (l : list A) (p: l <> []),
      l = init_safe l p ++ [last_safe l p].
  Proof.
    induction l; intros; simpl; [contradiction p; reflexivity |].
     

  Theorem tree_append : forall {A:Type} (tr1 : fingertree A) (tr2 : fingertree A),
    to_list (tr1 >< tr2) = to_list tr1 ++ to_list tr2.
  Proof.
    intros A tr1. induction tr1; intros; [reflexivity | |].
    - destruct tr2; [reflexivity | reflexivity |].
      simpl. destruct d; try reflexivity.
      simpl. do 2 (apply f_equal). apply @ft_reducer_addl with (F := node).
    - simpl in *. 
      remember (fun (nd : node A) (z : list A) =>
        match nd with
        | node2 a b => a :: b :: z
        | node3 a b c => a :: b :: c :: z
        end) as f.
      assert (forall (a1 : node A) (xs ys : list A), f a1 (xs ++ ys) = f a1 xs ++ ys);
        [intros; rewrite Heqf; destruct a1; reflexivity |].
      destruct tr2; simpl.
      + rewrite <- Heqf. rewrite app_nil_r. reflexivity.
      + destruct d0.
        * simpl. rewrite <- Heqf. rewrite app_cons.
          rewrite <- digit_reducer_app; [| reflexivity].
          rewrite (ft_reducer_app _ _ _ _ H). reflexivity.
        * simpl. rewrite <- Heqf. replace ([a0;a1;a])
          rewrite <- digit_reducer_app; [| reflexivity].
          rewrite (ft_reducer_app _ _ _ _ H). 
          
    - simpl in IHtr1. unfold to_list. cbv [reducer]. cbv [fingertree_reduce].
      
      cbv.
      simpl. destruct d, tr2, d0; simpl; try (rewrite app_nil_r; reflexivity).
      + apply f_equal. replace ([a1;a0]) with ([a1] ++ [a0]).
        * {rewrite ft_reducer_app.

           - reflexivity.
           - intros. destruct a2; reflexivity.
          }
        * reflexivity.


    - simpl in *. destruct tr2.
      + destruct d; (rewrite app_nil_r; reflexivity).
      + destruct d.
        * {simpl. destruct d0.
           - simpl. apply f_equal. destruct tr1.
             + reflexivity.
             + simpl. destruct n; reflexivity.
             + 
          }
         

  Theorem tree_append_assoc {A:Type}
          (tr1: fingertree A) (tr2: fingertree A) : fingertree A.
  Proof. Admitted.

  (* Oscar *)
    Fixpoint reverse_node {A: Type}{B: Type}
             (f: A -> B) (n: node A): node B  :=
      match n with
      | (node2  a b) => node2 (f b) (f a)
      | (node3 a b c) => node3 (f c) (f b) (f a)
    end.
    
   

  Fixpoint reverse_digit {A: Type}{B: Type}
           (f: A -> B) (d: digit A): digit B  :=
    match d with
    | one a => one (f a)
    | two a b => two (f b) (f a)
    | three a b c => three (f c) (f b) (f a)
    | four a b c d => four (f d) (f c) (f b) (f a)
    end.
  
  Fixpoint reverse_tree {A: Type}
           (f: A -> A)(tr: fingertree A) : fingertree A :=
    match tr with
    | empty => empty
    | single x => single (f x)
    | deep pr m sf =>
      deep (reverse_digit f sf) (reverse_tree (reverse_node f) m)
           (reverse_digit f pr)
    end.
    

  Definition reverse {A: Type} : fingertree A -> fingertree A :=
    reverse_tree (fun (x: A) => x).

   Example reverse_ex01 :
     reverse (single 1)  = single 1.
   
   Proof. reflexivity. Qed.
   
   Example reverse_ex02:forall (A : Type),
     reverse (@empty A)  = (@empty A).
   
  Example reverse_ex03 :
    reverse (deep (two 0 1) (single (node2 2 3)) (three 4 5 6)) =
            deep (three 6 5 4) (single (node2 3 2)) (two 1 0).
  Proof. unfold reverse. unfold reverse_tree. unfold reverse_digit.
  simpl. reflexivity. Qed.

  
    
  Theorem tree_reverse {A : Type} (tr : fingertree A) :
    to_list (reverse tr) = rev (to_list tr).

  Theorem tree_reverse_idem {A : Type} ...

   

        
  
      


End FingerTrees.



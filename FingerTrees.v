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

  Definition nd_reducer {A B : Type} : (A -> B -> B) -> node A -> B -> B :=
    fun op nd z => match nd with
                | node2 a b => op a (op b z)
                | node3 a b c => op a (op b (op c z))
                end.

  Definition nd_reducel {A B : Type} : (B -> A -> B) -> B -> node A -> B :=
    fun op z nd => match nd with
                | node2 a b => op (op z b) a
                | node3 a b c => op (op (op z c) b) a
                end.

  Lemma nd_reducer_app :
    forall {A B} (op : A -> list B -> list B) (a : node A) (xs ys : list B),
      (forall a (xs ys : list B), op a (xs ++ ys) = (op a xs) ++ ys) ->
      nd_reducer op a (xs ++ ys) = nd_reducer op a xs ++ ys.
  Proof.
    intros. destruct a; simpl; rewrite ?H; reflexivity.
  Qed.

  Instance node_reduce : reduce node :=
    {|
      reducer := @nd_reducer;
      reducel := @nd_reducel;
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
      reducer := @digit_reducer;
      reducel := @digit_reducel;
    |}.

  Fixpoint ft_reducer {A:Type} {B:Type}
             (op: A -> B -> B) (tr : fingertree A) (z : B) : B :=
      match tr with
      | empty => z
      | single x => op x z
      | deep pr m sf =>
        let op' := reducer op in
        let op'' := ft_reducer (reducer op) in
        op' pr (op'' m (op' sf z))
      end.

  Fixpoint ft_reducel {A:Type} {B:Type}
           (op: B -> A -> B) (z : B) (tr : fingertree A) : B :=
      match tr with
      | empty => z
      | single x => op z x
      | deep pr m sf =>
        let op'  := reducel op in
        let op'' := ft_reducel (reducel op) in
        op' (op'' (op' z pr) m) sf
      end.

  Instance fingertree_reduce : reduce fingertree :=
    {|
      reducer := @ft_reducer;
      reducel := @ft_reducel;
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

  Theorem digit_reducer_app :
    forall {A B : Type} (xs ys : list B) d (op : A -> list B -> list B),
      (forall a xs ys, op a (xs ++ ys) = (op a xs) ++ ys) ->
      (digit_reducer op d (xs ++ ys) = digit_reducer op d xs ++ ys).
  Proof.
    intros.
    destruct d; simpl; rewrite ?H; reflexivity.
  Qed.


  (* if you add an x to the left of a tree tr and then convert it to a list, it is
     the same as converting tr to a list and then consing x
  *)
  Lemma ft_reducer_addl : forall {A B : Type}  {F : Type -> Type}
                         (tr : fingertree (F A)) xs x
                         (op : F A -> B -> B),
      ft_reducer op (x <| tr) xs = op x (ft_reducer op tr xs).
  Proof.
    intros A B F tr.
    induction tr; intros; try reflexivity.
    destruct d; try reflexivity.  simpl.
    do 2 (apply f_equal). 
    specialize (IHtr (digit_reducer op d0 xs) (node3 a0 a1 a2) (nd_reducer op)).
    rewrite IHtr. reflexivity.
  Qed.

  Lemma ft_reducer_addr : forall {A B : Type}  {F : Type -> Type}
                         (tr : fingertree (F A)) xs x
                         (op : F A -> B -> B),
      ft_reducer op (tr |> x) xs = (ft_reducer op tr (op x xs)).
  Proof.
    intros A B F tr.
    induction tr; intros; simpl; [reflexivity | reflexivity |].
    destruct d0; simpl; try reflexivity.
    specialize (IHtr (op a2 (op x xs)) (node3 a a0 a1) (nd_reducer op)).
    rewrite IHtr. reflexivity.
  Qed.


  Theorem to_tree_to_list_id : forall {A:Type} (xs : list A),
      to_list (to_tree xs) = xs.
  Proof.
    intros. induction xs.
    - reflexivity.
    - simpl. rewrite (@ft_reducer_addl A (list A) (fun x => x) _ [] a _).
      apply f_equal. simpl in IHxs. assumption.
  Qed.

  (* Adam *)

  Inductive app3_list (A : Type) : Type :=
  | app3_two  : A -> A -> app3_list A
  | app3_three : A -> A -> A -> app3_list A
  | app3_four  : A -> A -> A -> A -> app3_list A
  | app3_more : A -> A -> A -> app3_list A -> app3_list A.

  Arguments app3_two {A} _ _.
  Arguments app3_three {A} _ _ _.
  Arguments app3_four {A} _ _ _ _.
  Arguments app3_more {A} _ _ _ _.

  Fixpoint a3_reducer {A B : Type} (op : A -> B -> B) (xs : app3_list A) (ys : B) : B :=
    match xs with
    | app3_two a b => op a (op b ys)
    | app3_three a b c => op a (op b (op c ys))
    | app3_four a b c d => op a (op b (op c (op d ys)))
    | app3_more a b c xs' => op a (op b (op c (a3_reducer op xs' ys)))
    end.

  Fixpoint a3_reducel {A B : Type} (op : B -> A -> B) (ys : B) (xs : app3_list A) : B :=
    match xs with
    | app3_two a b => op (op ys a) b
    | app3_three a b c => op (op (op ys a) b) c
    | app3_four a b c d => op (op (op (op ys a) b) c) d
    | app3_more a b c xs' => a3_reducel op (op (op (op ys a) b) c) xs'
    end.

  Instance a3_reduce : reduce app3_list :=
    {|
      reducer := @a3_reducer;
      reducel := @a3_reducel;
    |}.

  Fixpoint dig_app3 {A:Type} (ds1 : digit A) (ds2 : app3_list A) (ds3 : digit A): app3_list A :=
    match ds1, ds2, ds3 with
    | one a, app3_two b c, one d => app3_four a b c d
    | two a b, app3_two c d, one e => app3_more a b c (app3_two d e)
    | three a b c, app3_two d e, one f => app3_more a b c (app3_three d e f)
    | four a b c d, app3_two e f, one g => app3_more a b c (app3_four d e f g)
    | one a, app3_three b c, one d => app3_four a b c d
    | two a b, app3_three c d, one e => app3_more a b c (app3_two d e)
    | three a b c, app3_three d e, one f => app3_more a b c (app3_three d e f)
    | four a b c d, app3_three e f, one g => app3_more a b c (app3_four d e f g)


    to_list ds1 ++ ds2 ++ to_list ds3.

  Fixpoint nodes {A : Type} (xs : app3_list A) : list (node A) :=
    match xs with
    | app3_none => [] (* should never happen *)
    | app3_two a b => [node2 a b]
    | app3_three a b c => [node3 a b c]
    | app3_four a b c d => [node2 a b; node2 c d]
    | app3_more a b c xs' => node3 a b c :: nodes xs'
    end.

  Fixpoint app3 {A:Type} (tr1:fingertree A) (ds : list A) (tr2:fingertree A)
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


  Theorem ft_reducer_app :
    forall {A : Type} {F : Type -> Type}
      (tr : fingertree (F A)) (xs ys : list A)
      (op : F A -> list A -> list A),
      (forall a (xs ys : list A), op a (xs ++ ys) = (op a xs) ++ ys) ->
      ft_reducer op tr (xs ++ ys) = (ft_reducer op tr xs) ++ ys.
  Proof.
    intros A F tr. induction tr; intros; [reflexivity | apply H |]; simpl.
    - rewrite (digit_reducer_app xs ys d0 op H).
      rewrite IHtr.
      + remember (ft_reducer (nd_reducer op) tr (digit_reducer op d0 xs)) as xs'.
        apply (digit_reducer_app xs' ys d op H).
      + intros. apply nd_reducer_app. assumption.
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

  Lemma last_app : forall {A : Type} (xs : list A) x d,
      (x :: xs) = removelast (x :: xs) ++ [last (x :: xs) d].
  Proof.
    induction xs; [reflexivity |].
    intros. simpl. apply f_equal. simpl in IHxs. apply IHxs.
  Qed.

  Lemma to_list_fr_empty : forall {A B : Type} op (xs : list A) (ys : B),
      ft_reducer op (addl' xs empty) ys = ft_reducer op (to_tree xs) ys.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma to_list_fr_single : forall {A B : Type} a op (xs : list A) (ys : B),
      ft_reducer op (addl' xs (single a)) ys =
      ft_reducer op (to_tree xs) (op a ys).
  Proof.
    induction xs.
    - intros. reflexivity.
    - intros. simpl. rewrite @ft_reducer_addl with (F := fun x => x).
      simpl in IHxs. rewrite (ft_reducer_addl _ (op a ys) a0).
      rewrite IHxs. reflexivity.
  Qed.

  Lemma to_list_fr_deep : forall {A B : Type} op (xs : list A) (ys : B) pf sf m,
      ft_reducer op (addl' xs (deep pf m sf)) ys =
      ft_reducer op (to_tree xs) (ft_reducer op (deep pf m sf) ys).
  Proof.
    induction xs.
    - reflexivity.
    - intros. simpl in *. rewrite (ft_reducer_addl _ ys a op).
      remember (
          digit_reducer op pf (ft_reducer (nd_reducer op) m (digit_reducer op sf ys))
        ) as ys'.
      rewrite (ft_reducer_addl _ ys' a op). 
      rewrite IHxs. rewrite Heqys'. reflexivity.
  Qed.

  Theorem ft_reducer_addl' : forall {A B : Type} op (xs : list A) (ys : B) (tr : fingertree A),
      ft_reducer op (addl' xs tr) ys =
      ft_reducer op (to_tree xs) (ft_reducer op tr ys).
  Proof.
    destruct tr.
    - rewrite to_list_fr_empty. reflexivity.
    - rewrite to_list_fr_single. reflexivity.
    - rewrite to_list_fr_deep. reflexivity.
  Qed.

  Theorem ft_reducer_addr' : forall {A B : Type} op (xs : list A) (ys : B) (tr : fingertree A),
      ft_reducer op (addr' tr xs) ys =
      ft_reducer op tr (ft_reducer op (to_tree xs) ys).
  Proof.
    induction xs; intros; simpl in *; [reflexivity |].
    destruct tr; simpl.
    - rewrite (ft_reducer_addl (fold_right addl empty xs) ys a op).
      rewrite IHxs. reflexivity.
    - rewrite IHxs. simpl. rewrite (ft_reducer_addl _ ys a op). reflexivity.
    - rewrite IHxs. destruct d0;
                      simpl; rewrite (ft_reducer_addl _ ys a op); try reflexivity.
      rewrite (ft_reducer_addr tr _ (node3 a0 a1 a2) (nd_reducer op)).
      simpl. reflexivity.
  Qed.

  Lemma ft_reducer_deep : forall {A B : Type} op (m : fingertree (node A)) pf sf (ys : B),
      ft_reducer op (deep pf m sf) ys = digit_reducer op pf (ft_reducer (nd_reducer op) m (digit_reducer op sf ys)).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma app_sing : forall {A} (x y : A) xs, [x] = xs ++ [y] -> x = y /\ xs = [].
  Proof.
    intros. destruct xs; split.
    - inversion H. reflexivity.
    - reflexivity.
    - inversion H. contradiction (app_cons_not_nil xs [] y H2).
    - inversion H. contradiction (app_cons_not_nil xs [] y H2).
  Qed.

  Lemma nodes_to_list : forall {A B : Type} xs x1 x2 x3 x4 (op : A -> B -> B) ys,
      reducer (nd_reducer op) (nodes (x1 :: x2 :: x3 :: x4 :: xs)) ys =
      reducer op (x1 :: x2 :: x3 :: x4 :: xs) ys.
  Proof.
    intros A B xs. induction xs; intros; [reflexivity|].
    
    simpl. destruct xs; [reflexivity|].
    destruct xs; [reflexivity |].
    simpl in *. do 3 (apply f_equal).
    intros A B xs x1 x2. remember (x1 :: x2 :: xs). induction l; intros.
    - inversion Heql.
    - simpl in *. inversion Heql. destruct xs eqn:Hxs.
      + reflexivity.
      + inversion Heql. subst. simpl in *.
    - inversion Heql. destruct l.
      + inversion H1.
      + inversion H1. subst. simpl in *.
    [reflexivity|].
    - simpl in *. inversion Heql. subst.
      simpl in IHl.
    - simpl in *. destruct l.
      + simpl.
      + 


  Lemma dig_app3_to_list : forall {A B : Type} (m : list A) (op : A -> B -> B) (pf sf : digit A) (ys : B),
      ft_reducer (nd_reducer op) (to_tree (nodes (dig_app3 pf m sf))) ys =
      digit_reducer op pf (ft_reducer op (to_tree m) (digit_reducer op sf ys)).
  Proof.
    intros A B. induction m; intros.
    - destruct pf, sf; try reflexivity.
    - unfold to_tree. destruct pf, sf; simpl.
      + destruct (m ++ [a1]) eqn:Heq; symmetry in Heq; [contradiction (app_cons_not_nil m [] a1 Heq)|].
        induction l. 
        * simpl. rewrite (ft_reducer_addl _ _ a). 
          destruct (app_sing a2 a1 m Heq). subst. reflexivity.
        * 

        destruct l; do 20 (try (destruct l)); simpl.

        *  destruct (app_sing a2 a1 m Heq). subst.
          reflexivity.
        * rewrite (ft_reducer_addl _ _ a). . subst.
          reflexivity.
          
         
        * simpl. rewrite (ft_reducer_addl _ _ a). 

  (* problem is that the induction hyp wants op to be lifted
      into node, but it is not since digit_reducer.
     Maybe the problem is that A is mentioned in the fingertree,
   so the the inductive case puts an extra node that is not actually
   necessary. Just change to B as I have done below, but now we need
   to change all the auxiliary lemmas to be also be more general*)
  Theorem app3_to_list :
    forall {A B:Type} (op : A -> B -> B)
      (tr1 tr2 : fingertree A) xs (ys : B),
    ft_reducer op (app3 tr1 xs tr2) ys =
    ft_reducer op tr1 (ft_reducer op (to_tree xs) (ft_reducer op tr2 ys)).
  Proof.
    intros A B op tr1.
    Opaque addr' addl'. induction tr1; intros.
    - simpl. rewrite (@ft_reducer_addl' A B op xs ys tr2). reflexivity.
    - destruct tr2; simpl.
      + rewrite (ft_reducer_addr'). reflexivity.
      + rewrite (ft_reducer_addl _ ys a op).
        rewrite (@to_list_fr_single A B a0 op xs). reflexivity.
      + rewrite (ft_reducer_addl _ ys a op).
        rewrite (@to_list_fr_deep A B op xs ys d d0 tr2).
        reflexivity.
    - destruct tr2. 
      + simpl. rewrite ft_reducer_addr'. reflexivity.
      + simpl. rewrite (ft_reducer_addr _ _ a op).
        rewrite ft_reducer_addr'. reflexivity.
      + simpl in *.
        rewrite IHtr1.
        apply f_equal. rewrite <- ?ft_reducer_deep.
                           
        apply f_equal. destruct d0, d1; simpl.
        * {destruct (xs ++ [a0]) eqn:Hxs.
           - symmetry in Hxs. contradiction (app_cons_not_nil xs [] a0).
           - destruct l.
             + destruct xs; [simpl; inversion Hxs; reflexivity|].
               inversion Hxs. symmetry in H1. contradiction (app_cons_not_nil xs [] a0).
             + destruct l.
               * {simpl. destruct xs; [inversion Hxs|].
                  simpl. rewrite (ft_reducer_addl (fold_right addl empty xs)).
                  inversion Hxs. destruct xs.
                  - inversion H1. reflexivity.
                  - inversion H1. symmetry in H3. contradiction (app_cons_not_nil xs [] a0).
                  }
               * {simpl. destruct l.
                  - simpl. destruct xs; [inversion Hxs|].
                    destruct xs; [inversion Hxs|].
                    inversion Hxs. simpl. rewrite (ft_reducer_addl _ _ a1).
                    rewrite (ft_reducer_addl _ _ a2).
                    do 3 (apply f_equal).
                    rewrite ft_reducer_addl'. simpl.

                     inversion Hxs. simpl.
                  }

          }
       * 
        specialize (IHtr1 op tr2' (nodes (dig_app3 d0' xs d1'))).
      + rewrite IHtr1.
        apply f_equal.
        remember (ft_reducer (nd_reducer op) tr2 (digit_reducer op d2 ys)) as ys'.
        

        
        destruct (nodes (dig_app3 d0 xs d1)) eqn:Heq. 

        pose proof (ft_reducer_addl' op).
        rewrite (H xs _ empty).
        rewrite (H (nodes (dig_app3 d0 xs d1)) _ empty).
        
        simpl in H.
        
      + rewrite @ft_reducer_addr with (F:= fun x => x)(op := cons).
        rewrite ft_reducer_addr'. simpl.
        rewrite <- digit_reducer_app; [| intros; reflexivity].
        rewrite <- ft_reducer_app; [| destruct a0; reflexivity].
        rewrite <- digit_reducer_app; [| intros; reflexivity].
        reflexivity.
      + rewrite <- digit_reducer_app; [| intros; reflexivity].
        rewrite <- ft_reducer_app; [| destruct a; reflexivity].
        do 2 (rewrite <- digit_reducer_app; [| intros; reflexivity]).
        rewrite <- ft_reducer_app; [| destruct a; reflexivity].
        simpl in *. 
        reflexivity.





      

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
      + destruct d0;
          simpl; rewrite <- Heqf; try (rewrite last_app with (x := a0) (d0 := a0); 
          rewrite <- digit_reducer_app; [| reflexivity];
          rewrite (ft_reducer_app _ _ _ _ H); reflexivity).
        rewrite <- digit_reducer_app; [| reflexivity].
        rewrite ft_reducer_addr. rewrite Heqf. rewrite <- Heqf. 
        rewrite <- ft_reducer_app; [reflexivity |].
        intros. rewrite Heqf. destruct a4; reflexivity.
      + rewrite <- Heqf.
        specialize (IHtr1 
        
         

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
  Proof.
    intros. induction tr; intros; try reflexivity.
    simpl. destruct (reverse_digit (fun x : A => x) d0).
    - destruct d, d0.
      + simpl.  (* apply ft_reducer_app *)
  
    
  Theorem tree_reverse_idem {A : Type} ...

   

        
  
      


End FingerTrees.



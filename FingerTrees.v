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

  Instance digit_reduce : reduce digit :=
    {|
      reducer := fun _ _ op dg z => match dg with
                                 | one a => op a z
                                 | two a b => op a (op b z)
                                 | three a b c => op a (op b (op c z))
                                 | four a b c d => op a (op b (op c (op d z)))
                                 end;
      reducel := fun _ _ op z dg => match dg with
                                 | one a => op z a
                                 | two a b => op (op z a) b
                                 | three a b c => op (op (op z a) b) c
                                 | four a b c d => op (op (op (op z a) b) c) d
                                 end;
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

  Lemma view_l_addl : forall {A : Type} tr (x y : A) xs,
      (view_l tr = cons_l x xs) -> view_l (addl y tr) = cons_l y (addl x xs).
  Proof.
    intros A tr. induction tr; intros.
    - inversion H.
    - inversion H. subst. simpl. reflexivity.
    - simpl. destruct d.
      + inversion H. subst. destruct (view_l tr), d0.
        * {simpl. inversion H. destruct (view_l tr) eqn:Heq.
           - rewrite (view_l_nil_empty tr) in Heq. subst.
             inversion H. Abort.

  Definition collapse_nodelist {A:Type} {F : Type -> Type} {r : reduce F}
             (xs : list (F A)) : list A :=
    fold_right (fun nd l => to_list nd ++ l) [] xs.

  Example collapse_nodelist_ex01 :
    collapse_nodelist [node2 0 1; node3 2 3 4] = [0;1;2;3;4].
  Proof. reflexivity. Qed.

  (* if you add an x to the left of a tree tr and then convert it to a list, it is
     the same as converting tr to a list and then consing x
  *)
  Lemma to_list_cons : forall {A : Type}  {F : Type -> Type}
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
    remember (match d0 with 
             | one a3 => op a3 xs
             | two a3 b => op a3 (op b xs)
             | three a3 b c => op a3 (op b (op c xs))
             | four a3 b c d => op a3 (op b (op c (op d xs)))
              end) as d0match.
    specialize (IHtr d0match (node3 a0 a1 a2) l).
    rewrite IHtr. rewrite Heql. reflexivity.
  Qed.


  Theorem to_tree_to_list_id : forall {A:Type} (xs : list A),
      to_list (to_tree xs) = xs.
  Proof.
    intros. induction xs.
    - reflexivity.
    - simpl. rewrite @to_list_cons with (op := cons) (F := fun x => x).
      apply f_equal. simpl in IHxs. assumption.
  Qed.

  (* Adam *)
  Fixpoint append {A:Type}
           (tr1 : fingertree A) (tr2 : fingertree A) : fingertree A.
  Proof. Admitted.

  Theorem tree_append {A:Type} (tr1 : fingertree A) (tr2 : fingertree A) :
    to_list (append tr1 tr2) = to_list tr1 ++ to_list tr2.

  Theorem tree_append_assoc {A:Type} ...

  (* Oscar *)
  Fixpoint reverse {A: Type} (tr : fingertree A) : fingertree A.
  Proof. Admitted.

  Theorem tree_reverse {A : Type} (tr : fingertree A) :
    to_list (reverse tr) = rev (to_list tr).

  Theorem tree_reverse_idem {A : Type} ...

   

        
  
      


End FingerTrees.



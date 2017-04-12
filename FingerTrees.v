Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import Basics.   

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

  Instance id_reduce : reduce (fun A => A) :=
    {|
      reducer := fun _ _ fn xs z => fn xs z;
      reducel := fun _ _ fn z xs => fn z xs
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
                | node2 b a => op (op z b) a
                | node3 c b a => op (op (op z c) b) a
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
    | two b a => op (op z b) a
    | three c b a => op (op (op z c) b) a
    | four d c b a => op (op (op (op z d) c) b) a
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

  Lemma view_l_nil_empty : forall {A : Type} (tr : fingertree A), view_l tr = nil_l <-> tr = empty.
  Proof.
    intros. split.
    - intros. destruct tr; [reflexivity | inversion H |]. simpl in H.
      destruct d, (view_l tr), d0; inversion H.
    - intros. destruct tr; [reflexivity | inversion H |].
      destruct d, (view_l tr), d0; inversion H.
  Qed.

  Lemma to_tree_empty : forall {A : Type}, @is_empty A (to_tree []).
  Proof.
    intros. simpl. unfold is_empty. destruct (view_l empty) eqn:Heq.
    - apply I.
    - inversion Heq.
  Qed.

  Lemma addl_not_empty : forall {A : Type} (tr : fingertree A) x, ~(addl x tr = empty).
  Proof.
    intros A tr x H. induction tr; inversion H.
    destruct d; inversion H1.
  Qed.

  Lemma addl_not_2single : forall {A : Type} (x y z : A), ~(addl x (single y) = single z).
  Proof.
    intros A x y z H. simpl in H. inversion H.
  Qed.

  Lemma addr_not_empty : forall {A : Type} (tr : fingertree A) x, ~(addr tr x = empty).
    intros A tr x H. induction tr; inversion H.
    destruct d0; inversion H1.
  Qed.

  Lemma addl_not_nil : forall {A : Type} (tr : fingertree A) x,
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

  Theorem digit_reducer_app :
    forall {A B : Type} (xs ys : list B) d (op : A -> list B -> list B),
      (forall a xs ys, op a (xs ++ ys) = (op a xs) ++ ys) ->
      (digit_reducer op d (xs ++ ys) = digit_reducer op d xs ++ ys).
  Proof.
    intros.
    destruct d; simpl; rewrite ?H; reflexivity.
  Qed.


  (* if you add an x to the left of a tree tr and then convert it to a list, it is
     the same as converting tr to a list and then consing x.
     This is the general version of the above.
     to_list (x <| tr) = x :: (to_list tr) <=>
     ft_reducer cons (x <| tr) [] = cons x (tr_reducer cons tr [])
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
    apply (IHtr (digit_reducer op d0 xs) (node3 a0 a1 a2) (nd_reducer op)).
  Qed.

  Lemma ft_reducer_addr : forall {A B : Type}  {F : Type -> Type}
                         (tr : fingertree (F A)) xs x
                         (op : F A -> B -> B),
      ft_reducer op (tr |> x) xs = (ft_reducer op tr (op x xs)).
  Proof.
    intros A B F tr.
    induction tr; intros; simpl; [reflexivity | reflexivity |].
    destruct d0; simpl; try reflexivity.
    rewrite (IHtr (op a2 (op x xs)) (node3 a a0 a1) (nd_reducer op)).
    reflexivity.
  Qed.


  Theorem to_tree_to_list_id : forall {A:Type} (xs : list A),
      to_list (to_tree xs) = xs.
  Proof.
    intros. induction xs; [reflexivity |].
    simpl. rewrite (@ft_reducer_addl A (list A) (fun x => x) _ [] a _).
    apply f_equal. simpl in IHxs. assumption.
  Qed.

  (**
     We need this data structure to represent lists that can be converted into
     lists of nodes in a total way
  **)
  Inductive app3_list (A : Type) : Type :=
  | app3_two   : A -> A -> app3_list A
  | app3_three : A -> A -> A -> app3_list A
  | app3_four  : A -> A -> A -> A -> app3_list A
  | app3_more  : A -> A -> A -> app3_list A -> app3_list A.

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

  (**
     Yeah, this is a doosie, but I don't know how to define it in more succint terms
     while still retaining its total properties.
     In the original paper, this is much simpler since we do not have to use an
     app3_list and can write partial functions, but we cannot do proper proofs
     if we do this (believe me, I've wasted many hours on trying).
   **)
  Fixpoint dig_app3 {A:Type} (d1 : digit A) (xs : list A) (d2 : digit A): app3_list A :=
    match d1, xs, d2 with
    | one a,        [], one b        => app3_two a b
    | one a,        [], two b c      => app3_three a b c
    | one a,        [], three b c d  => app3_four a b c d
    | one a,        [], four b c d e => app3_more a b c (app3_two d e)

    | two a b,      [], one c        => app3_three a b c
    | two a b,      [], two c d      => app3_four a b c d
    | two a b,      [], three c d e  => app3_more a b c (app3_two d e)
    | two a b,      [], four c d e f => app3_more a b c (app3_three d e f)

    | three a b c,  [], one d        => app3_four a b c d
    | three a b c,  [], two d e      => app3_more a b c (app3_two d e)
    | three a b c,  [], three d e f  => app3_more a b c (app3_three d e f)
    | three a b c,  [], four d e f g => app3_more a b c (app3_four d e f g)

    | four a b c d, [], one e        => app3_more a b c (app3_two d e)
    | four a b c d, [], two e f      => app3_more a b c (app3_three d e f)
    | four a b c d, [], three e f g  => app3_more a b c (app3_four d e f g)
    | four a b c d, [], four e f g h => app3_more a b c (app3_more d e f (app3_two g h))

    | one a,        (x :: xs), _     => dig_app3 (two a x) xs d2
    | two a b,      (x :: xs), _     => dig_app3 (three a b x) xs d2
    | three a b c,  (x :: xs), _     => dig_app3 (four a b c x) xs d2
    | four a b c d, (x :: xs), _     => app3_more a b c (dig_app3 (two d x) xs d2)
    end.

  (**
     group a list of A's into a list of nodes of A'
     uses the app3_list data type to ensure totality and make proofs
     about nodes possible
   **)
  Fixpoint nodes {A : Type} (xs : app3_list A) : list (node A) :=
    match xs with
    | app3_two a b        => [node2 a b]
    | app3_three a b c    => [node3 a b c]
    | app3_four a b c d   => [node2 a b; node2 c d]
    | app3_more a b c xs' => node3 a b c :: nodes xs'
    end.


  (**
     append two fingertrees with a list of "remainder-values".
     This does all the hard work of append. Should be amortized logarithmic time
   **)
  Fixpoint app3 {A:Type} (tr1:fingertree A) (ds : list A) (tr2:fingertree A)
    : fingertree A :=
    match tr1, tr2 with
    | empty, _ => addl' ds tr2
    | _, empty => addr' tr1 ds
    | single x, _ => x <| addl' ds tr2
    | _, single x => addr' tr1 ds |> x
    | deep pr1 m1 sf1, deep pr2 m2 sf2 =>
        let ds' := dig_app3 sf1 ds pr2 in
        deep pr1 (app3 m1 (nodes ds') m2) sf2
    end.

  Definition append {A:Type}
           (tr1 : fingertree A) (tr2 : fingertree A) : fingertree A :=
    app3 tr1 [] tr2.

  
  Notation "t1 >< t2" := (append t1 t2)
                     (at level 62, left associativity).

  
  (**
     reducing a ft with an accumulator that is the concatenation of two
     lists xs and ys, is the same as just reducing with xs and then appending ys
     given that the operation we use for reduction has the same property
   **)
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
      ft_reducer op (deep pf m sf) ys =
      digit_reducer op pf (ft_reducer (nd_reducer op) m (digit_reducer op sf ys)).
  Proof.
    intros. reflexivity.
  Qed.

  (**
     to_list (nodes xs) = xs
     reducer (nd_reducer cons) [] = xs
  **)
  Lemma nodes_reducer : forall {A B : Type} xs (op : A -> B -> B) ys,
      reducer (nd_reducer op) (nodes xs) ys =
      reducer op xs ys.
  Proof.
    induction xs; intros; simpl in *; try reflexivity.
    rewrite IHxs. reflexivity.
  Qed.

  Lemma nodes_to_list : forall {A B : Type} xs (op : A -> B -> B) ys,
      reducer (nd_reducer op) (to_tree (nodes xs)) ys =
      reducer op (to_tree xs) ys.
  Proof.
    intros A B xs. induction xs; intros; simpl in *; try reflexivity.
    rewrite (ft_reducer_addl _ _ (node3 a a0 a1) _). simpl.
    rewrite 3!(ft_reducer_addl _ _ _ op). rewrite IHxs. reflexivity.
  Qed.

  Lemma dig_app3_to_list : forall {A B : Type} (m : list A) (op : A -> B -> B) (pf sf : digit A) (ys : B),
      ft_reducer (nd_reducer op) (to_tree (nodes (dig_app3 pf m sf))) ys =
      digit_reducer op pf (ft_reducer op (to_tree m) (digit_reducer op sf ys)).
  Proof.
    intros A B. induction m; intros.
    - destruct pf, sf; try reflexivity.
    - simpl. destruct pf; simpl in *;
               try (rewrite IHm; simpl; rewrite (ft_reducer_addl _ _ a _); reflexivity).
      rewrite (ft_reducer_addl _ _ (node3 a0 a1 a2) _). simpl.
      rewrite (ft_reducer_addl _ _ a _ ). do 3 (apply f_equal).
      simpl in *.  rewrite IHm. reflexivity.
  Qed.

  (**
     reducing over app3 tr1 xs tr2 "distributes"
  **)
  Theorem app3_to_list :
    forall {A B:Type} (op : A -> B -> B) (tr1 tr2 : fingertree A) xs (ys : B),
    ft_reducer op (app3 tr1 xs tr2) ys =
    ft_reducer op tr1 (ft_reducer op (to_tree xs) (ft_reducer op tr2 ys)).
  Proof.
    intros A B op tr1.
    Opaque addl' addr'. induction tr1; intros.
    - simpl. rewrite (ft_reducer_addl' op xs ys tr2). reflexivity.
    - destruct tr2; simpl.
      + rewrite (ft_reducer_addr'). reflexivity.
      + rewrite (ft_reducer_addl _ ys a op).
        rewrite (to_list_fr_single a0 op xs). reflexivity.
      + rewrite (ft_reducer_addl _ ys a op).
        rewrite (to_list_fr_deep op xs ys d d0 tr2).
        reflexivity.
    - destruct tr2. 
      + simpl. rewrite ft_reducer_addr'. reflexivity.
      + simpl. rewrite (ft_reducer_addr _ _ a op).
        rewrite ft_reducer_addr'. reflexivity.
      + simpl in *.
        rewrite IHtr1.
        apply f_equal. rewrite <- ?ft_reducer_deep.
        pose proof (@dig_app3_to_list A B). simpl in *. rewrite H.
        reflexivity.
        Transparent addr' addl'.
  Qed.

  (**
     appending to trees and converting the to lists is the same as converting
     them to lists separately and appending the lists together
   **)
  Theorem tree_append : forall {A:Type} (tr1 : fingertree A) (tr2 : fingertree A),
    to_list (tr1 >< tr2) = to_list tr1 ++ to_list tr2.
  Proof.
    intros A tr1 tr2. simpl. unfold "><". rewrite app3_to_list. simpl.
    rewrite <- (ft_reducer_app tr1 ); [reflexivity |].
    intros. reflexivity.
  Qed.

  (**
     appending two trees is associative with respect to to_list
  **)
  Theorem tree_append_assoc : forall {A B : Type} (tr1 tr2 tr3 : fingertree A)
                                (op : A -> B -> B) ys,
  reducer op (tr1 >< (tr2 >< tr3)) ys = reducer op ((tr1 >< tr2) >< tr3) ys.
  Proof.
    intros A B tr1. unfold "><".
    induction tr1; intros; rewrite ?app3_to_list; reflexivity.
  Qed.

  Theorem tree_append_assoc_to_list :
    forall {A B : Type} (tr1 tr2 tr3 : fingertree A),
      to_list (tr1 >< (tr2 >< tr3)) = to_list ((tr1 >< tr2) >< tr3).
  Proof.
    intros. simpl. apply tree_append_assoc.
  Qed.

  Theorem tree_append_assoc_sum :
    forall {A : Type} (tr1 tr2 tr3 : fingertree nat),
      reducer plus (tr1 >< (tr2 >< tr3)) 0 = reducer plus ((tr1 >< tr2) >< tr3) 0.
  Proof.
    intros. simpl. apply tree_append_assoc.
  Qed.

      
  Class reversable F := Reversable {
                            mirror {A:Type} (fn:A -> A) : (F A) -> F A
                          }.

  Instance reversable_id : reversable (fun A => A) :=
    {|
      mirror := fun _ _ x => x
    |}.


  (* Oscar *)
    Fixpoint reverse_node {A: Type}
             (f: A -> A) (n: node A): node A  :=
      match n with
      | (node2  a b)  => node2 (f b) (f a)
      | (node3 a b c) => node3 (f c) (f b) (f a)
      end.

  Instance reversable_node : reversable node :=
    {|
      mirror := @reverse_node;
    |}.

   
  Fixpoint reverse_digit {A: Type}
           (f: A -> A) (d: digit A): digit A  :=
    match d with
    | one a        => one (f a)
    | two a b      => two (f b) (f a)
    | three a b c  => three (f c) (f b) (f a)
    | four a b c d => four (f d) (f c) (f b) (f a)
    end.

  (* Instance reversable_digit : reversable digit := *)
  (*   {| *)
  (*     mirror := @reverse_digit; *)
  (*   |}. *)
  
  Fixpoint reverse_tree {A: Type} 
           (f: A -> A)(tr: fingertree A) : fingertree A :=
    match tr with
    | empty        => empty
    | single x     => single (f x)
    | deep pr m sf =>
      deep (reverse_digit f sf) (reverse_tree (reverse_node f) m)
           (reverse_digit f pr)
    end.

  (* Instance reversable_tree : reversable fingertree := *)
  (*   {| *)
  (*     mirror := @reverse_tree; *)
  (*   |}. *)
    

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



  Definition reverse_simple {A : Type} (tr:fingertree A) : fingertree A :=
    reducer (flip addr) tr empty.
  
  Compute (reverse_simple (to_tree [1;2;3;4;5;6;7;8;9;10])).

  Compute (reducer cons (reverse_tree (reverse_node (fun x => x)) (single (node2 1 2))) []).
  Compute (to_list (reverse_simple (single (node2 1 2)))).


  Definition node_map {A B : Type} (f : A -> B) (nd : node A) : node B :=
    match nd with
    | node2 a b => node2 (f a) (f b)
    | node3 a b c => node3 (f a) (f b) (f c)
    end.

  Definition digit_map {A B : Type} (f : A -> B) (d : digit A) : digit B :=
    match d with
    | one a => one (f a)
    | two a b => two (f a) (f b)
    | three a b c => three (f a) (f b) (f c)
    | four a b c d => four (f a) (f b) (f c) (f d)
    end.

  Fixpoint tree_map {A B : Type} (f : A -> B) (tr : fingertree A) : fingertree B :=
    match tr with
    | empty => empty
    | single x => single (f x)
    | deep pf m sf => deep (digit_map f pf) (tree_map (node_map f) m) (digit_map f sf)
    end.


  Example map_tree_ex01 :
    to_list (tree_map (plus 1) (to_tree [1;2;3;4;5])) = [2;3;4;5;6].
  Proof. reflexivity. Qed.

  Lemma map_addl {A : Type} (tr : fingertree A) :
    forall B (f: A -> B) x, tree_map f (x <| tr) = f x <| tree_map f tr.
  Proof.
    induction tr; intros; try reflexivity.
    destruct d, d0; simpl; try (rewrite IHtr); try reflexivity.
  Qed.

  Lemma map_addr {A : Type} (tr : fingertree A) :
    forall B (f: A -> B) x, tree_map f (tr |> x) = tree_map f tr |> f x .
  Proof.
    induction tr; intros; try reflexivity.
    destruct d, d0; simpl; try (rewrite IHtr); try reflexivity.
  Qed.

  Lemma reverse_addl {A : Type} (tr : fingertree A) :
    forall x fn, reverse_tree fn (x <| tr) = reverse_tree fn tr |> fn x.
  Proof.
    unfold reverse. induction tr; simpl in *; intros; try reflexivity.
    destruct d; try reflexivity.
    simpl in *. rewrite IHtr. reflexivity.
  Qed.

  Compute (reducel (flip cons) [] [1;2;3]).

  Definition red_cons {A : Type} {F : Type -> Type} {r:reduce F} (x:F A) (xs:list A) :
    list A := to_list x ++ xs.

  Theorem reverse_reduce_list {A B : Type} (l : list A) :
    forall acc, reducer cons l acc = reducel (flip cons) acc (rev l).
  Proof.
    induction l; intros; simpl; try reflexivity.
    simpl in *. rewrite IHl. 
    


  Theorem reverse_reducer_inj {A : Type} (tr : fingertree A) :
    forall B (op : A -> list B -> list B) acc fn,
      reducer op (reverse_tree fn tr) acc =
      reducel (flip cons) acc (reducer op (tree_map fn tr) []).
  Proof.
    unfold reverse. induction tr; intros.
    - reflexivity.
    - simpl. 
    - Opaque rev tree_map. simpl in *.
      specialize (IHtr (nd_reducer op) (digit_reducer op (reverse_digit fn d) acc)).
      rewrite IHtr. Focus 2.
      intros. destruct d.
      + simpl.  split.
        * {destruct a.
           - simpl. destruct (H a1), (H a). 
           }

        * simpl.
  Theorem reverse_reducer_inj {A : Type} {F : Type -> Type} (tr : fingertree (F A)) :
    forall fn (lift : (A -> list A -> list A) -> (F A -> list A -> list A)) acc,
      reducer (cons) (reverse_tree fn tr) (rev acc) =
      rev acc ++ rev (reducer (cons) tr []).
  Proof.
    induction tr; intros; simpl in *.
    - symmetry. apply app_nil_r.
    - 

  Lemma map_reverse_simpl {A : Type} (tr : fingertree A) :
    forall B (f : A -> B) (acc : fingertree A) (op : forall {C}, C -> fingertree C -> fingertree C)
      (pf : forall a acc, op (f a) (tree_map f acc) = tree_map f (op a acc)),
      reducer op (tree_map f tr) (tree_map f acc) =
      tree_map f (reducer op tr acc).
  Proof.
    induction tr; intros; simpl in *; try reflexivity.
    - apply pf.
    - specialize (IHtr (node B) (node_map f) _ (fun T => nd_reducer (op T))).
      
    - destruct d, d0; simpl in *.
      + rewrite (IHtr _ (node_map f) (op B (f a0) (tree_map f acc))).
     [unfold flip; rewrite map_addr; reflexivity|].
    - 
    unfold reverse_simple in *. simpl in *.

  (**
     We need to map the fn over the tree because the tree data-type is non-regular.
  **)
  Lemma reverse_reverse_simple {A B: Type} (tr: fingertree A) :
    forall (op : A -> B -> B) acc (fn : A -> A),
    reducer op (reverse_tree fn tr) acc =
    reducer op (reverse_simple (tree_map fn tr)) acc.
  Proof.
    induction tr; try reflexivity.
    intros. simpl in *. rewrite IHtr. simpl.
    unfold reverse_simple, reducer, flip. simpl.
    destruct d, d0; try reflexivity.
    - simpl in *. 
      rewrite (ft_reducer_addr _ _ (fn a) _).
      simpl.
      destruct tr; try reflexivity.
      + destruct n; reflexivity.
      + rewrite IHtr. simpl.
      rewrite (ft_reducer_addr _ _ _ _).
      
    - unfold reverse_simple. unfold reducer. simpl.
      
    remember (digit_reducer op (reverse_digit fn d) acc) as acc'.
    specialize (IHtr (nd_reducer op) acc' (reverse_node fn)).
    rewrite IHtr.
        
  Theorem tree_reverse_reduce {A B : Type} (tr: fingertree A) :
          forall (xs : B) (op: A -> B -> B) fn,
    reducer op (reverse_tree fn tr) xs = reducel (flip op) xs tr.
  Proof.
    induction tr; intros; simpl in *; try reflexivity.

    Theorem tree_reverse {A : Type} (tr : fingertree A) :
    reducer cons (reverse tr) [] = rev (redu.
  Proof.
    intros. induction tr; intros; simpl; try reflexivity.
    simpl in *.
    simpl. destruct (reverse_digit (fun x : A => x) d0).
    - destruct d, d0.
      + simpl in *.  (* apply ft_reducer_app *)
  
    
  Theorem tree_reverse_idem {A : Type} ...

   

        
  
      


End FingerTrees.



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

  Definition toList {F: Type -> Type} {r: reduce F} {A : Type} (s : F A) : list A :=
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

  Definition digit (A:Type) := list A.

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
    | single b => deep [a] empty [b]
    | deep [b;c;d;e] m sf => deep [a;b] (addl (node3 c d e) m) sf
    | deep pr m sf => deep (a :: pr) m sf
    end.


  Fixpoint addr {A:Type} (tr:fingertree A) (a:A) : fingertree A  :=
    match tr with
    | empty => single a
    | single b => deep [b] empty [a]
    | deep pr m [e;d;c;b] => deep pr (addr m (node3 e d c)) [b;a]
    | deep pr m sf => deep pr m (sf ++ [a])
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

  Definition toTree {F:Type -> Type} {A:Type} {r:reduce F} (s:F A) :
    fingertree A := addl' s empty.

  Inductive View_l (S:Type -> Type) (A:Type): Type :=
  | nil_l : View_l S A
  | cons_l : A -> S A -> View_l S A.

  Arguments nil_l {S} {A}.
  Arguments cons_l {S} {A} _ _.

  Fixpoint view_l {A:Type} (tr:fingertree A) : View_l fingertree A :=
    match tr with
    | empty => nil_l
    | single x => cons_l x empty
    | deep (x::pr') m sf => cons_l x (deep_l (tl (x::pr')) m sf)
    | deep _ _ _ => nil_l (* nonsense case *)
    end
    with deep_l {A:Type} (pr:digit A) m (sf:digit A) := match pr with
                          | [] => match view_l m with
                                 | nil_l => toTree sf
                                 | cons_l a m' => deep (toList a) m' sf
                                 end
                          | _  => deep pr m sf
                          end.







End FingerTrees.



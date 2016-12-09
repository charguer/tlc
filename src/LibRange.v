(**************************************************************************
* TLC: A library for Coq                                                  *
* Intervals as sets                                                       *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import LibTactics LibLogic LibReflect
  LibOperation LibStruct LibInt LibOrder
  LibEpsilon LibRelation LibSet.
Require Export LibBag.

Class Range_incl_excl A := { range_incl_excl : A -> A -> set A }.
Class Range_incl_incl A := { range_incl_incl : A -> A -> set A }.
Class Range_excl_excl A := { range_excl_excl : A -> A -> set A }.
Class Range_excl_incl A := { range_excl_incl : A -> A -> set A }.

Global Instance Range_incl_excl_le `{Le A} : Range_incl_excl A.
Proof. constructor. apply (fun x y => set_st (fun a => x <= a < y)). Defined.

Global Instance Range_incl_incl_le `{Le A} : Range_incl_incl A.
Proof. constructor. apply (fun x y => set_st (fun a => x <= a <= y)). Defined.

Global Instance Range_excl_excl_le `{Le A} : Range_excl_excl A.
Proof. constructor. apply (fun x y => set_st (fun a => x < a < y)). Defined.

Global Instance Range_excl_incl_le `{Le A} : Range_excl_incl A.
Proof. constructor. apply (fun x y => set_st (fun a => x < a <= y)). Defined.

Lemma Range_incl_excl_le_def :
  forall `{Le A} (x y : A),
  range_incl_excl x y = set_st (fun a => x <= a < y).
Proof. reflexivity. Qed.

Lemma Range_incl_incl_le_def :
  forall `{Le A} (x y : A),
  range_incl_incl x y = set_st (fun a => x <= a <= y).
Proof. reflexivity. Qed.

Lemma Range_excl_excl_le_def :
  forall `{Le A} (x y : A),
  range_excl_excl x y = set_st (fun a => x < a < y).
Proof. reflexivity. Qed.

Lemma Range_excl_incl_le_def :
  forall `{Le A} (x y : A),
  range_excl_incl x y = set_st (fun a => x < a <= y).
Proof. reflexivity. Qed.

Global Opaque Range_incl_excl_le Range_incl_incl_le Range_excl_excl_le Range_excl_incl_le.

Notation "'\set[' a , b )" := (range_incl_excl a b)
  (at level 0, format "'\set[' a ,  b )").
Notation "'\set[' a , b ]" := (range_incl_incl a b)
  (at level 0, format "'\set[' a ,  b ]").
Notation "'\set(' a , b )" := (range_excl_excl a b)
  (at level 0, format "'\set(' a ,  b )").
Notation "'\set(' a , b ]" := (range_excl_incl a b)
  (at level 0, format "'\set(' a ,  b ]").

Goal forall (n: Z), 0 < n -> \set[0, n) = \{0} \u \set[1, n-1].
Abort.

Goal forall (n: Z), 0 < n -> \set(0, n) = \{1} \u \set(1, n-1].
Abort.

Lemma range_incl_excl_split :
  forall `{Le A} (a b c : A),
  Le_total_order ->
  a <= b <= c ->
  \set[a, c) = \set[a, b) \u \set[b, c).
Proof using.
  introv M L.
  do 3 (rewrite Range_incl_excl_le_def).
  apply in_extens. intro x.
  rewrite in_union_eq.
  do 3 (rewrite in_set_st_eq).
  iff P.
  - destruct (case_le_gt b x) as [C|C].
    right*. left*.
  - destruct P as [P|P].
    forwards*: lt_le_trans b x c.
    forwards*: le_trans b a x. (* TODO: le_le_trans = le_trans *)
Qed.
(**************************************************************************
* TLC: A library for Coq                                                  *
* Order relations                                                         *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibReflect LibOperation LibRelation.
Generalizable Variables A.


(**************************************************************************)
(* * Preorder *)

(** Definition *)

Record preorder A (R:binary A) : Prop := {
   preorder_refl : refl R;
   preorder_trans : trans R }.

Arguments preorder_trans [A] [R] [p] y [x] [z].

(** Transformations *)

Lemma preorder_inverse : forall A (R:binary A),
  preorder R ->
  preorder (inverse R).
Proof using. hint trans_inverse. introv [Re Tr]. constructor~. Qed.

Lemma preorder_rclosure : forall A (R:binary A),
  preorder R ->
  preorder (rclosure R).
Proof using. hint refl_rclosure, trans_rclosure. introv [Re Tr]. constructor~. Qed.


(**************************************************************************)
(* * Total preorder *)

(** Definition of total preorder relations *)

Record total_preorder A (R:binary A) : Prop := {
   total_preorder_trans : trans R;
   total_preorder_total : total R }.

Arguments total_preorder_trans [A] [R] t y [x] [z].

(** Conversion to preorder *)

Lemma total_preorder_refl : forall A (le:binary A),
  total_preorder le ->
  refl le.
Proof using. introv [Tr To]. intros x. destruct~ (To x x). Qed.

#[global]
Hint Resolve total_preorder_refl.

Coercion total_preorder_to_preorder A (R:binary A)
  (O:total_preorder R) : preorder R.
Proof using. lets [M _]: O. constructor~. Qed.

#[global]
Hint Resolve total_preorder_to_preorder.

(** Transformations *)

Lemma total_preorder_inverse : forall A (R:binary A),
  total_preorder R ->
  total_preorder (inverse R).
Proof using. hint trans_inverse, total_inverse. introv [Tr To]. constructor~. Qed.

Lemma total_preorder_rclosure : forall A (R:binary A),
  total_preorder R ->
  total_preorder (rclosure R).
Proof using. hint trans_rclosure, total_rclosure. introv [Re Tr]. constructor~. Qed.

(** Properties *)

Lemma inverse_of_not : forall A (R:binary A) x y,
  total R ->
  ~ R x y ->
  inverse R x y.
Proof using. introv T H. destruct (T x y); auto_false~. Qed.

Lemma inverse_strict_of_not : forall A (R:binary A) x y,
  total R ->
  ~ R x y ->
  inverse (strict R) x y.
Proof using.
  introv T H. destruct (T x y). auto_false~.
  hnf. split~. intro_subst~.
Qed.


(**************************************************************************)
(* * Order *)

(** Definition *)

Record order A (R:binary A) : Prop := {
   order_refl : refl R;
   order_trans : trans R;
   order_antisym : antisym R }.

Arguments order_trans [A] [R] [o] y [x] [z].
Arguments order_antisym [A] [R] [o] [x] [y].

(** Conversion to preorder *)

Coercion order_to_preorder A (R:binary A)
  (O:order R) : preorder R.
Proof using. destruct* O. constructors*. Qed.

#[global]
Hint Resolve order_to_preorder.

(** Transformations *)

Lemma order_inverse : forall A (R:binary A),
  order R ->
  order (inverse R).
Proof using.
  hint trans_inverse, antisym_inverse.
  introv [Re Tr An]. constructor~.
Qed.

Lemma order_rclosure : forall A (R:binary A),
  order R ->
  order (rclosure R).
Proof using.
  hint refl_rclosure, trans_rclosure, antisym_rclosure.
  introv [Re Tr An]. constructor~.
Qed.

(** Properties *)


(* ********************************************************************** *)
(** * Order relation upto an equivalence relation *)

(** Note: this is used in LibFix *)

Record order_wrt (A:Type) (E:binary A) (R:binary A) : Prop := {
   order_wrt_refl : refl R;
   order_wrt_trans : trans R;
   order_wrt_antisym : antisym_wrt E R }.

Arguments order_wrt_trans [A] [E] [R] [o] y [x] [z].
Arguments order_wrt_antisym [A] [E] [R] [o] [x] [y].

(** Conversion to preorder *)

Coercion order_wrt_to_preorder A (E:binary A) (R:binary A)
  (O:order_wrt E R) : preorder R.
Proof using. destruct* O. constructors*. Qed.

#[global]
Hint Resolve order_wrt_to_preorder.

(** Transformations *)

Lemma order_wrt_inverse : forall A (E:binary A) (R:binary A),
  order_wrt E R ->
  order_wrt E (inverse R).
Proof using.
  hint trans_inverse, antisym_wrt_inverse.
  introv [Re Tr An]. constructor~.
Qed.

Lemma order_wrt_rclosure : forall A (E:binary A) (R:binary A),
  order_wrt E R ->
  order_wrt (rclosure E) (rclosure R).
Proof using.
  hint refl_rclosure, trans_rclosure, antisym_wrt_rclosure.
  introv [Re Tr An]. constructor~.
Qed.

(** Properties *)


(**************************************************************************)
(* * Total Order *)

(** Definition *)

Record total_order A (R:binary A) : Prop := {
   total_order_order : order R;
   total_order_total : total R }.

(** Projections *)

Definition total_order_refl := order_refl.
Definition total_order_trans := order_trans.
Definition total_order_antisym := order_antisym.

Arguments total_order_trans [A] [R] [o] y [x] [z].
Arguments total_order_antisym [A] [R] [o] [x] [y].

(** Construction *)

Lemma total_order_intro : forall A (R:binary A),
   trans R ->
   antisym R ->
   total R ->
   total_order R.
Proof using.
  introv Tra Ant Tot. constructor~. constructor~.
  intros_all. destruct~ (Tot x x).
Qed.

(** Conversion to order *)

Coercion total_order_to_total_preorder A (R:binary A)
  (O:total_order R) : total_preorder R.
Proof using. destruct* O. constructors*. applys* order_trans. Qed.

Definition total_order_to_order := total_order_order.

#[global]
Hint Resolve total_order_to_order total_order_to_total_preorder.

(** Transformations *)

Lemma total_order_inverse : forall A (R:binary A),
  total_order R ->
  total_order (inverse R).
Proof using.
  hint total_inverse, order_inverse.
  introv [Or To]. constructor~.
Qed.

Lemma total_order_rclosure : forall A (R:binary A),
  total_order R ->
  total_order (rclosure R).
Proof using.
  hint total_rclosure, order_rclosure.
  introv [Or To]. constructor~.
Qed.

(** Properties *)

Section TotalOrderProp.
Variables (A:Type) (R : binary A).

(** WARNING: notations here are not typeclass operators
    -- TODO: is this really what we want?
    perhaps it would be clearer to inline these notations. *)

Notation "'le'" := (R).
Notation "'ge'" := (inverse R).
Notation "'lt'" := (strict R).
Notation "'gt'" := (inverse lt).

Ltac total_order_normalize :=
  repeat rewrite rclosure_eq_fun;
  repeat rewrite inverse_eq_fun;
  repeat rewrite strict_eq_fun.

Lemma total_order_le_is_rclosure_lt : forall (To:total_order R),
  le = rclosure lt.
Proof using.
  extens. intros. total_order_normalize. iff M.
  tests~: (x = y).
  destruct M. autos*. subst*. dintuition eauto.
Qed.

Lemma total_order_lt_is_strict_le : forall (To:total_order R),
  lt = strict le.
Proof using.
  auto.
Qed.

Lemma total_order_ge_is_rclosure_gt : forall (To:total_order R),
  ge = rclosure gt.
Proof using.
  extens. intros. total_order_normalize. iff M.
  tests~: (x = y).
  destruct M. autos*. subst*. dintuition eauto.
Qed.

Lemma total_order_gt_is_strict_ge : forall (To:total_order R),
  gt = strict ge.
Proof using.
  extens. intros. total_order_normalize. iff M.
  tests~: (x = y).
  destruct M. autos*.
  destruct M. autos*.
Qed.

Lemma total_order_lt_or_eq_or_gt : forall (To:total_order R) x y,
  lt x y \/ x = y \/ gt x y.
Proof using.
  introv H. intros. total_order_normalize. tests: (x = y).
    branch~ 2.
    destruct (total_order_total H x y).
     branch~ 1.
     branch~ 3.
Qed.

Lemma total_order_lt_or_ge : forall (To:total_order R) x y,
  lt x y \/ ge x y.
Proof using.
  intros. branches (total_order_lt_or_eq_or_gt To x y).
  left~.
  right~. subst. hnf. apply~ total_order_refl.
  right~. rewrite~ total_order_ge_is_rclosure_gt.
   total_order_normalize. hnfs~.
Qed.

Lemma total_order_le_or_gt : forall (To:total_order R) x y,
  le x y \/ gt x y.
Proof using.
  intros. branches~ (total_order_lt_or_eq_or_gt To x y).
  left~. rewrite~ total_order_le_is_rclosure_lt. total_order_normalize. hnfs~.
  left~. subst. apply~ total_order_refl.
Qed.

End TotalOrderProp.


(**************************************************************************)
(* * Strict order *)

(** Definition *)

Record strict_order A (R:binary A) : Prop := {
   strict_order_irrefl : irrefl R;
   strict_order_asym : asym R;
   strict_order_trans : trans R }.

Arguments strict_order_trans [A] [R] [s] y [x] [z].

(** Transformations *)

Lemma strict_order_inverse : forall A (R:binary A),
  strict_order R ->
  strict_order (inverse R).
Proof using.
  hint antisym_inverse, trans_inverse, asym_inverse.
  introv [Ir As Tr]. constructor~.
Qed.

Lemma strict_order_strict : forall A (R:binary A),
  order R ->
  strict_order (strict R).
Proof using.
  introv [Re As Tr]. unfold strict. constructor; intros_all; simpls.
  destruct* H.
  applys* antisym_inv x y.
  split. applys* As. intros E. subst. applys* antisym_inv y z.
Qed.

Lemma order_rclosure_of_strict_order : forall A (R:binary A),
  strict_order R ->
  order (rclosure R).
Proof using.
  introv [Re As Tr]. rewrite rclosure_eq_fun. constructor; simpl.
  intros_all~.
  introv [H1|E1] [H2|E2]; subst; auto.
    left. apply* trans_inv.
  introv [H1|E1] [H2|E2]; try subst; auto.
    false. apply* As.
Qed.


(**************************************************************************)
(* * Total strict order *)

(** Definition *)

Record strict_total_order A (R:binary A) : Prop := {
   strict_total_order_trans : trans R;
   strict_total_order_trichotomous : trichotomous R }.

Arguments strict_total_order_trans [A] [R] [s] y [x] [z].

(** Conversion to strict order and back *)

Lemma strict_total_order_irrefl : forall A (R:binary A),
  strict_total_order R ->
  irrefl R.
Proof using. introv [Tr Tk]. intros x. lets: (Tk x x). inverts~ H. Qed.

Lemma strict_total_order_asym : forall A (R:binary A),
  strict_total_order R ->
  asym R.
Proof using. introv [Tr Tk]. intros x y. lets: (Tk x y). inverts~ H. Qed.

Coercion strict_total_order_to_strict_order A (R:binary A)
  (O:strict_total_order R) : strict_order R.
Proof using.
  lets [M _]: O. constructor;
  autos~ strict_total_order_irrefl strict_total_order_asym.
Qed.

#[global]
Hint Resolve strict_total_order_to_strict_order.

(** Transformation *)

Lemma strict_total_order_inverse : forall A (R:binary A),
  strict_total_order R ->
  strict_total_order (inverse R).
Proof using.
  introv [Tr Tk]. constructor. apply~ trans_inverse.
  apply~ trichotomous_inverse.
Qed.
(** From total order *)

Lemma strict_total_order_of_total_order : forall A (R:binary A),
  total_order R ->
  strict_total_order (strict R).
Proof using.
  introv [[Re Tr As] To]. constructor.
  apply~ trans_strict.
  intros x y. tests: (x = y).
    subst. apply trichotomy_eq. unfolds* strict.
    unfold strict. destruct (To x y).
      apply* trichotomy_left.
      apply* trichotomy_right.
Qed.


(* ********************************************************************** *)
(** * Definition of order operators *)

(* ---------------------------------------------------------------------- *)
(** ** Classes and notation for comparison operators *)

(** Operators *)

Class Le (A : Type) := { le : binary A }.
Class Ge (A : Type) := { ge : binary A }.
Class Lt (A : Type) := { lt : binary A }.
Class Gt (A : Type) := { gt : binary A }.

Global Opaque le lt ge gt.

(** Structures *)

Class Le_preorder `{Le A} : Prop :=
  { le_preorder : preorder le }.

Class Le_total_preorder `{Le A} : Prop :=
  { le_total_preorder : total_preorder le }.

Class Le_order `{Le A} : Prop :=
  { le_order : order le }.

Class Le_total_order `{Le A} : Prop :=
  { le_total_order : total_order le }.

Class Lt_strict_order `{Lt A} : Prop :=
  { lt_strict_order : strict_order lt }.

Class Lt_strict_total_order `{Lt A} : Prop :=
  { lt_strict_total_order : strict_total_order lt }.

(** Notation *)

Declare Scope comp_scope.

Notation "x <= y" := (le x y)
  (at level 70, no associativity) : comp_scope.
Notation "x >= y" := (ge x y)
  (at level 70, no associativity) : comp_scope.
Notation "x < y" := (lt x y)
  (at level 70, no associativity) : comp_scope.
Notation "x > y" := (gt x y)
  (at level 70, no associativity) : comp_scope.

Open Scope comp_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z)
  (at level 70, y at next level) : comp_scope.
Notation "x <= y < z" := (x <= y /\ y < z)
  (at level 70, y at next level) : comp_scope.
Notation "x < y <= z" := (x < y /\ y <= z)
  (at level 70, y at next level) : comp_scope.
Notation "x < y < z" := (x < y /\ y < z)
  (at level 70, y at next level) : comp_scope.


(* ---------------------------------------------------------------------- *)
(** ** The operators [ge], [lt] and [gt] are deduced from [le] *)

#[global]
Instance ge_of_le : forall `{Le A}, Ge A.
  constructor. apply (inverse le). Defined.
#[global]
Instance lt_of_le : forall `{Le A}, Lt A.
  constructor. apply (strict le). Defined.
#[global]
Instance gt_of_le : forall `{Le A}, Gt A.
  constructor. apply (inverse lt). Defined.

Lemma ge_is_inverse_le : forall `{Le A}, ge = inverse le.
Proof using. extens*. Qed.

Lemma lt_is_strict_le : forall `{Le A}, lt = strict le.
Proof using. extens*. Qed.

Lemma gt_is_inverse_lt : forall `{Le A}, gt = inverse lt.
Proof using. extens*. Qed.

Lemma gt_is_inverse_strict_le : forall `{Le A}, gt = inverse (strict le).
Proof using. extens. intros. rewrite gt_is_inverse_lt. rewrite* lt_is_strict_le. Qed.

Global Opaque ge_of_le lt_of_le gt_of_le.

(** Local tactic [rew_to_le] *)

#[global]
Hint Rewrite @gt_is_inverse_strict_le @ge_is_inverse_le @lt_is_strict_le : rew_to_le.

Tactic Notation "rew_to_le" :=
  autorewrite with rew_to_le in *.

#[global]
Hint Rewrite @ge_is_inverse_le @gt_is_inverse_lt : rew_to_le_lt.

Tactic Notation "rew_to_le_lt" :=
  autorewrite with rew_to_le_lt in *.

Lemma gt_is_strict_inverse_le : forall `{Le A},
  gt = strict (inverse le).
Proof using. intros. rew_to_le. apply inverse_strict. Qed.

Lemma le_is_rclosure_lt : forall `{Le A},
  refl le ->
  le = rclosure lt.
Proof using. intros. rew_to_le. rewrite~ rclosure_strict. Qed.

Lemma le_is_inverse_ge : forall `{Le A},
  le = inverse ge.
Proof using. intros. rew_to_le. rewrite~ inverse_inverse. Qed.

Lemma lt_is_inverse_gt : forall `{Le A},
  lt = inverse gt.
Proof using. intros. rew_to_le. rewrite~ inverse_inverse. Qed.

Lemma gt_is_strict_ge : forall `{Le A},
  gt = strict ge.
Proof using. intros. rew_to_le. apply inverse_strict. Qed.

Lemma ge_is_rclosure_gt : forall `{Le A},
  refl le ->
  ge = rclosure gt.
Proof using. intros. rewrite gt_is_strict_ge. rewrite~ rclosure_strict. Qed.


(* ********************************************************************** *)
(** * Classes for comparison properties *)

(* ---------------------------------------------------------------------- *)
(** ** Definition of classes *)

(** symmetric structure *)

Class Ge_preorder `{Le A} : Prop :=
  { ge_preorder : preorder ge }.
Class Ge_total_preorder `{Le A} : Prop :=
  { ge_total_preorder : total_preorder ge }.
Class Ge_order `{Le A} : Prop :=
  { ge_order : order ge }.
Class Ge_total_order `{Le A} : Prop :=
  { ge_total_order : total_order le }.
Class Gt_strict_order `{Le A} : Prop :=
  { gt_strict_order : strict_order gt }.
Class Gt_strict_total_order `{Le A} : Prop :=
  { gt_strict_total_order : strict_total_order gt }.

(** properties of le *)

Class Le_refl `{Le A} :=
  { le_refl : refl le }.
Class Le_trans `{Le A} :=
  { le_trans : trans le }.
Class Le_antisym `{Le A} :=
  { le_antisym : antisym le }.
Class Le_total `{Le A} :=
  { le_total : total le }.

(** properties of ge *)

Class Ge_refl `{Ge A} :=
  { ge_refl : refl ge }.
Class Ge_trans `{Ge A} :=
  { ge_trans : trans ge }.
Class Ge_antisym `{Ge A} :=
  { ge_antisym : antisym ge }.
Class Ge_total `{Ge A} :=
  { ge_total : total ge }.

(** properties of lt *)

Class Lt_irrefl `{Lt A} :=
  { lt_irrefl : irrefl lt }.
Class Lt_trans `{Lt A} :=
  { lt_trans : trans lt }.

(** properties of gt *)

Class Gt_irrefl `{Gt A} :=
  { gt_irrefl : irrefl gt }.
Class Gt_trans `{Gt A} :=
  { gt_trans : trans gt }.

(** mixed transitivity results *)

Class Lt_le_trans `{Le A} :=
  { lt_le_trans : forall y x z, x < y -> y <= z -> x < z }.
Class Le_lt_trans `{Le A} :=
  { le_lt_trans : forall y x z, x <= y -> y < z -> x < z }.
Class Gt_ge_trans `{Le A} :=
  { gt_ge_trans : forall y x z, x > y -> y >= z -> x > z }.
Class Ge_gt_trans `{Le A} :=
  { ge_gt_trans : forall y x z, x >= y -> y > z -> x > z }.

Arguments lt_irrefl [A] [H] [Lt_irrefl].
Arguments le_trans {A} {H} {Le_trans} y [x] [z].
Arguments ge_trans {A} {H} {Ge_trans} y [x] [z].
Arguments lt_trans {A} {H} {Lt_trans} y [x] [z].
Arguments gt_trans {A} {H} {Gt_trans} y [x] [z].

(** conversion between operators *)

Class Ge_as_sle `{Le A} : Prop :=
  { ge_as_sle : forall x y : A, (x >= y) = (y <= x) }.

Class Gt_as_slt `{Le A} : Prop :=
  { gt_as_slt : forall x y : A, (x > y) = (y < x) }.

Class Ngt_as_sle `{Le A} : Prop :=
  { ngt_as_sle : forall x y : A, (~ x < y) = (y <= x) }.

Class Nlt_as_ge `{Le A} : Prop :=
  { nlt_as_ge : forall x y : A, (~ x < y) = (x >= y) }.

Class Ngt_as_le `{Le A} : Prop :=
  { ngt_as_le : forall x y : A, (~ x > y) = (x <= y) }.

Class Nle_as_gt `{Le A} : Prop :=
  { nle_as_gt : forall x y : A, (~ x <= y) = (x > y) }.

Class Nge_as_lt `{Le A} : Prop :=
  { nge_as_lt : forall x y : A, (~ x >= y) = (x < y) }.

(** inclusion between operators *)

Class Lt_to_le `{Le A} : Prop :=
  { lt_to_le : forall x y : A, (x < y) -> (x <= y) }.

Class Gt_to_ge `{Le A} : Prop :=
  { gt_to_ge : forall x y : A, (x > y) -> (x >= y) }.

Class Nle_to_sle `{Le A} : Prop :=
  { nle_to_sle : forall x y : A, (~ x <= y) -> (y <= x) }.

Class Nle_to_slt `{Le A} : Prop :=
  { nle_to_slt : forall x y : A, (~ x <= y) -> (y < x) }.

(** case analysis *)

Class Case_eq_lt_gt `{Le A} : Prop :=
  { case_eq_lt_gt : forall x y : A, x = y \/ x < y \/ x > y }.

Class Case_eq_lt_slt `{Le A} : Prop :=
  { case_eq_lt_slt : forall x y : A, x = y \/ x < y \/ y < x }.

Class Case_le_gt `{Le A} : Prop :=
  { case_le_gt : forall x y : A, x <= y \/ x > y }.

Class Case_le_slt `{Le A} : Prop :=
  { case_le_slt : forall x y : A, x <= y \/ y < x }.

Class Case_lt_ge `{Le A} : Prop :=
  { case_lt_ge : forall x y : A, x < y \/ x >= y }.

Class Case_lt_sle `{Le A} : Prop :=
  { case_lt_sle : forall x y : A, x < y \/ y <= x }.

(** case analysis under one assumption *)

Class Neq_case_lt_gt `{Le A} : Prop :=
  { neq_case_lt_gt : forall x y : A, x <> y -> x < y \/ x > y }.

Class Neq_case_lt_slt `{Le A} : Prop :=
  { neq_case_lt_slt : forall x y : A, x <> y -> x < y \/ y < x }.

Class Le_case_eq_lt `{Le A} : Prop :=
  { le_case_eq_lt : forall x y : A, x <= y -> x = y \/ x < y }.

Class Ge_case_eq_gt `{Le A} : Prop :=
  { ge_case_eq_gt : forall x y : A, x >= y -> x = y \/ x > y }.

(** case analysis under two assumptions *)

Class Le_neq_to_lt `{Le A} : Prop :=
  { le_neq_to_lt : forall x y : A, x <= y -> x <> y -> x < y }.

Class Ge_neq_to_gt `{Le A} : Prop :=
  { ge_neq_to_gt : forall x y : A, x >= y -> x <> y -> x > y }.

Class Nlt_nslt_to_eq `{Le A} : Prop :=
  { nlt_nslt_to_eq : forall x y : A, ~ (lt x y) -> ~ (lt y x) -> x = y }.

(** contradiction from case analysis *)

Class Lt_ge_false `{Le A} : Prop :=
  { lt_ge_false : forall x y : A, x < y -> x >= y -> False }.

Class Lt_gt_false `{Le A} : Prop :=
  { lt_gt_false : forall x y : A, x < y -> x > y -> False }.

Class Lt_slt_false `{Le A} : Prop :=
  { lt_slt_false : forall x y : A, x < y -> y < x -> False }.


(* ********************************************************************** *)
(* * Instances for comparison structures *)

Section Instances.
Context `{Le A}.

Ltac auto_star ::= try solve [ dauto ].

(** derived structures *)

Global Instance Le_preorder_of_Le_order :
  Le_order ->
  Le_preorder.
Proof using. constructor. intros. apply* order_to_preorder. Qed.

Global Instance Le_total_preorder_of_Le_total_order :
  Le_total_order ->
  Le_total_preorder.
Proof using. constructor. intros. apply* total_order_to_total_preorder. Qed.

Global Instance Le_preorder_of_Total_preorder :
  Le_total_preorder ->
  Le_preorder.
Proof using. constructor. intros. apply* total_preorder_to_preorder. Qed.

Global Instance Le_order_of_Le_total_order :
  Le_total_order ->
  Le_order.
Proof using. constructor. intros. apply* total_order_to_order. Qed.

Global Instance lt_strict_order_of_lt_strict_total_order :
  Lt_strict_total_order ->
  Lt_strict_order.
Proof using. constructor. intros. apply* strict_total_order_to_strict_order. Qed.

Global Instance Lt_strict_order_of_Le_order :
  Le_order ->
  Lt_strict_order.
Proof using. constructor. intros. rew_to_le. apply* strict_order_strict. Qed.

Global Instance Lt_strict_total_order_of_Le_total_order :
  Le_total_order ->
  Lt_strict_total_order.
Proof using. constructor. intros. rew_to_le. apply* strict_total_order_of_total_order. Qed.

(** symmetric structures *)

Global Instance Ge_preorder_of_Le_order :
  Le_order ->
  Ge_preorder.
Proof using. constructor. rew_to_le. apply preorder_inverse. apply le_preorder. Qed.

Global Instance Ge_total_preorder_of_Le_total_order :
  Le_total_order ->
  Ge_total_preorder.
Proof using. constructor. rew_to_le. apply total_preorder_inverse. apply le_total_preorder. Qed.

Global Instance Ge_preorder_of_Total_preorder :
  Le_total_preorder ->
  Ge_preorder.
Proof using. constructor. rew_to_le. apply preorder_inverse. apply le_preorder. Qed.

Global Instance Ge_order_of_Le_total_order :
  Le_total_order ->
  Ge_order.
Proof using. constructor. rew_to_le. apply order_inverse. apply le_order. Qed.

Global Instance Gt_strict_order_of_lt_strict_total_order :
  Lt_strict_total_order ->
  Gt_strict_order.
Proof using. constructor. rewrite gt_is_inverse_lt. apply strict_order_inverse. apply lt_strict_order. Qed.

Global Instance Gt_strict_order_of_Le_order :
  Le_order ->
  Gt_strict_order.
Proof using. constructor. rewrite gt_is_inverse_lt. apply strict_order_inverse. apply lt_strict_order. Qed.

Global Instance Gt_strict_total_order_of_Le_total_order :
  Le_total_order ->
  Gt_strict_total_order.
Proof using. constructor. rewrite gt_is_inverse_lt. apply strict_total_order_inverse. apply lt_strict_total_order. Qed.

(** properties of le *)

Global Instance Le_refl_of_Le_preorder :
  Le_preorder ->
  Le_refl.
Proof using. intros [[Re Tr]]. constructor~. Qed.

Global Instance Le_trans_of_Le_preorder :
  Le_preorder ->
  Le_trans.
Proof using. intros [[Re Tr]]. constructor~. Qed.

Global Instance Le_antisym_of_Le_order :
  Le_order ->
  Le_antisym.
Proof using. constructor. intros. apply* order_antisym. Qed.

Global Instance Le_total_of_Le_total_order :
  Le_total_order ->
  Le_total.
Proof using. constructor. intros. apply* total_order_total. Qed.

(** properties of ge *)

Global Instance Ge_refl_of_Le_preorder :
  Le_preorder ->
  Ge_refl.
Proof using. constructor. rew_to_le. apply refl_inverse. apply le_refl. Qed.

Global Instance Ge_trans_of_Le_preorder :
  Le_preorder ->
  Ge_trans.
Proof using. constructor. rew_to_le. apply trans_inverse. apply le_trans. Qed.

Global Instance Ge_antisym_of_Le_order :
  Le_order ->
  Ge_antisym.
Proof using. constructor. rew_to_le. apply antisym_inverse. apply le_antisym. Qed.

Global Instance Ge_total_of_Le_total_order :
  Le_total_order ->
  Ge_total.
Proof using. constructor. rew_to_le. apply total_inverse. apply le_total. Qed.

(** properties of lt *)

Global Instance Lt_irrefl_of_Le_order :
  Le_order ->
  Lt_irrefl.
Proof using. constructor. apply strict_order_irrefl. apply lt_strict_order. Qed.

Global Instance Lt_trans_of_Le_order :
  Le_order ->
  Lt_trans.
Proof using. constructor. apply strict_order_trans. apply lt_strict_order. Qed.

(** properties of gt *)

Global Instance Gt_irrefl_of_Le_order :
  Le_order ->
  Gt_irrefl.
Proof using. constructor. apply strict_order_irrefl. apply gt_strict_order. Qed.

Global Instance Gt_trans_of_Le_order :
  Le_order ->
  Gt_trans.
Proof using. constructor. apply strict_order_trans. apply gt_strict_order. Qed.

(** mixed transitivity results *)

Global Instance Lt_le_trans_of_Le_order :
  Le_order ->
  Lt_le_trans.
Proof using.
  constructor. introv K L. rew_to_le. destruct K as [U V].
  split~. apply* le_trans. intro_subst. apply V. apply* le_antisym.
Qed.

Global Instance Le_lt_trans_of_Le_order :
  Le_order ->
  Le_lt_trans.
Proof using.
  constructor. introv K L. rew_to_le. destruct L as [U V].
  split~. apply* le_trans. intro_subst. apply V. apply* le_antisym.
Qed.

Global Instance gt_ge_trans_of_Le_order :
  Le_order ->
  Gt_ge_trans.
Proof using.
  constructor. introv K L. rew_to_le_lt. hnf in *. apply* le_lt_trans.
Qed.

Global Instance ge_gt_trans_of_Le_order :
  Le_order ->
  Ge_gt_trans.
Proof using.
  constructor. introv K L. rew_to_le_lt. hnf in *. apply* lt_le_trans.
Qed.
(** conversion between operators *)

Global Instance Ge_as_sle_of :
  Ge_as_sle.
Proof using. constructor. intros. rew_to_le. auto. Qed.

Global Instance Gt_as_slt_of :
  Gt_as_slt.
Proof using. constructor. intros. rew_to_le. auto. Qed.

Global Instance Ngt_as_sle_of_Le_total_order :
  Le_total_order ->
  Ngt_as_sle.
Proof using.
  constructor. intros. rew_to_le. unfold strict. rew_logic. iff M.
  destruct M.
    forwards K:(inverse_strict_of_not (R:=le)); eauto.
      apply le_total. apply (proj1 K).
    subst. apply le_refl.
  apply or_classic_l. intros P Q. apply P. apply* le_antisym.
Qed.

Global Instance Nlt_as_ge_of_Le_total_order :
  Le_total_order ->
  Nlt_as_ge.
Proof using. constructor. intros. rew_to_le_lt. unfold inverse. apply ngt_as_sle. Qed.

Global Instance Ngt_as_le_of_Le_total_order :
  Le_total_order ->
  Ngt_as_le.
Proof using. constructor. intros. rew_to_le_lt. unfold inverse. apply ngt_as_sle. Qed.

Global Instance Nle_as_gt_of_Le_total_order :
  Le_total_order ->
  Nle_as_gt.
Proof using.
  constructor. intros. rew_to_le_lt. unfold inverse.
  rewrite <- ngt_as_sle. rewrite~ not_not_eq.
Qed.

Global Instance Nge_as_lt_of_Le_total_order :
  Le_total_order ->
  Nge_as_lt.
Proof using.
  constructor. intros. rew_to_le_lt. unfold inverse.
  rewrite nle_as_gt. rewrite~ gt_is_inverse_lt.
Qed.

(** inclusion between operators *)

Global Instance Lt_to_le_of :
  Lt_to_le.
Proof using. constructor. intros. rew_to_le. unfolds* strict. Qed.

Global Instance Gt_to_ge_of :
  Gt_to_ge.
Proof using. constructor. intros. rew_to_le. unfolds* inverse, strict. Qed.

Global Instance Nle_to_sle_of_Le_total_order :
  Le_total_order ->
  Nle_to_sle.
Proof using.
  constructor. introv K. rewrite nle_as_gt in K.
  rew_to_le. unfolds* inverse, strict.
Qed.

Global Instance Nle_to_slt_of_Le_total_order :
  Le_total_order ->
  Nle_to_slt.
Proof using.
  constructor. introv K. rewrite nle_as_gt in K.
  rew_to_le. unfolds* inverse, strict.
Qed.

(** case analysis under no assumption *)

Global Instance Case_eq_lt_gt_of_Le_total_order :
  Le_total_order ->
  Case_eq_lt_gt.
Proof using.
  introv K. constructor. intros.
  lets [(M1&M2)|[M|(M1&M2)]]: (total_order_lt_or_eq_or_gt le_total_order x y).
    rewrite le_is_rclosure_lt in M1 by applys* total_order_refl. destruct* M1.
    autos*.
    rewrite le_is_rclosure_lt in M1 by applys* total_order_refl. destruct* M1.
Qed.

Global Instance Case_eq_lt_slt_of_Le_total_order :
  Le_total_order ->
  Case_eq_lt_slt.
Proof using.
  constructor. intros. pattern lt at 2. rewrite lt_is_inverse_gt.
  apply case_eq_lt_gt.
Qed.

Global Instance Case_le_gt_of_Le_total_order :
  Le_total_order ->
  Case_le_gt.
Proof using.
  constructor. intros.
  rewrite le_is_rclosure_lt by applys* total_order_refl. rewrite rclosure_eq.
  branches (total_order_lt_or_eq_or_gt le_total_order x y); eauto.
Qed.

Global Instance Case_eq_lt_ge_of_Le_total_order :
  Le_total_order ->
  Case_lt_ge.
Proof using.
  constructor. intros.
  rewrite ge_is_rclosure_gt by applys* total_order_refl. rewrite rclosure_eq.
  branches (total_order_lt_or_eq_or_gt le_total_order x y); eauto.
Qed.

Global Instance Case_le_slt_of_Le_total_order :
  Le_total_order ->
  Case_le_slt.
Proof using. constructor. intros. rewrite lt_is_inverse_gt. apply case_le_gt. Qed.

Global Instance Case_eq_lt_sle_of_Le_total_order :
  Le_total_order ->
  Case_lt_sle.
Proof using. constructor. intros. rewrite le_is_inverse_ge. apply case_lt_ge. Qed.


(** case analysis under one assumption *)

Global Instance Neq_case_lt_gt_of_Le_total_order :
  Le_total_order ->
  Neq_case_lt_gt.
Proof using. constructor. intros. destruct* (case_eq_lt_gt x y). Qed.

Global Instance Neq_case_lt_slt_of_Le_total_order :
  Le_total_order ->
  Neq_case_lt_slt.
Proof using. constructor. intros. destruct* (case_eq_lt_gt x y). Qed.

Global Instance Le_case_eq_lt_of_Le_total_order :
  Le_total_order ->
  Le_case_eq_lt.
Proof using. constructor. intros. rew_to_le. unfold strict. tests*: (x = y). Qed.

Global Instance Ge_case_eq_gt_of_Le_total_order :
  Le_total_order ->
  Ge_case_eq_gt.
Proof using. constructor. intros. rew_to_le. unfold inverse, strict. tests*: (x = y). Qed.

(** case analysis under two assumptions *)

Global Instance Le_neq_to_lt_of_Le_total_order :
  Le_total_order ->
  Le_neq_to_lt.
Proof using. constructor. intros. rew_to_le. hnfs*. Qed.

Global Instance Ge_neq_to_gt_of_Le_total_order :
  Le_total_order ->
  Ge_neq_to_gt.
Proof using. constructor. intros. rew_to_le. hnfs*. Qed.

Global Instance Nlt_nslt_to_eq_of_Le_total_order :
  Le_total_order ->
  Nlt_nslt_to_eq.
Proof using. constructor. intros. branches* (case_eq_lt_gt x y). Qed.

(** contradiction from case analysis *)

Global Instance Lt_ge_false_of_Le_total_order :
  Le_total_order ->
  Lt_ge_false.
Proof using. constructor. introv H1 H2. rewrite~ <- nlt_as_ge in H2. Qed.

Global Instance Lt_gt_false_of_Le_total_order :
  Le_total_order ->
  Lt_gt_false.
Proof using.
  constructor. introv H1 H2. rewrite~ <- nle_as_gt in H2.
  apply H2. apply* lt_to_le.
Qed.

Global Instance Lt_slt_false_of_Le_total_order :
  Le_total_order ->
  Lt_slt_false.
Proof using.
  constructor. introv H1 H2. rewrite <- gt_as_slt in H2.
  apply* lt_gt_false.
Qed.

End Instances.


(** -- Other lemmas needs arguments to be implicit? *)


(* ********************************************************************** *)
(** * Boolean comparison *)

Module BooleanComparison.

Open Scope comp_scope.

(** Additional notation for reflected boolean comparison.
    Use [Open Scope comp_scope_reflect] to use them. *)

Declare Scope comp_scope_reflect.

Notation "x ''<=' y" := (isTrue (@le _ _ x y))
  (at level 70, no associativity) : comp_scope_reflect.
Notation "x ''>=' y" := (isTrue (@ge _ _ x y))
  (at level 70, no associativity) : comp_scope_reflect.
Notation "x ''<' y" := (isTrue (@lt _ _ x y))
  (at level 70, no associativity) : comp_scope_reflect.
Notation "x ''>' y" := (isTrue (@gt _ _ x y))
  (at level 70, no associativity) : comp_scope_reflect.

End BooleanComparison.


(* ********************************************************************** *)
(** * Order on relations and on predicates *)

Lemma order_rel_incl : forall A B,
  order (@rel_incl A B).
Proof using.
  hint refl_rel_incl, antisym_rel_incl, trans_rel_incl.
  constructors*.
Qed.

Lemma order_pred_incl : forall A B,
  order (@rel_incl A B).
Proof using.
  hint refl_rel_incl, antisym_rel_incl, trans_rel_incl.
  constructors*.
Qed.


(* ********************************************************************** *)
(* * Min and max *)

Definition min `{Le A} (n m:A) : A :=
  If n <= m then n else m.

Lemma min_l : forall `{Le A} (n m:A),
  antisym le ->
  n <= m ->
  min n m = n.
Proof using. introv T M. unfold min. case_if*. Qed.

Lemma min_r : forall `{Le A} (n m:A),
  antisym le ->
  m <= n ->
  min n m = m.
Proof using. introv T M. unfold min. case_if*. Qed.

Definition max `{Le A} (n m:A) : A :=
  If n <= m then m else n.

Lemma max_l : forall `{Le A} (n m:A),
  antisym le ->
  n >= m ->
  max n m = n.
Proof using. introv T M. unfold max. case_if*. Qed.

Lemma max_r : forall `{Le A} (n m:A),
  antisym le ->
  n <= m ->
  max n m = m.
Proof using. introv T M. unfold max. case_if*. Qed.

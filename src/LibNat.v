(**************************************************************************
* TLC: A library for Coq                                                  *
* Naturals                                                                *
**************************************************************************)

Set Implicit Arguments.
Require Export Coq.Arith.Arith Coq.micromega.Lia.
From TLC Require Import LibTactics LibReflect LibBool LibOperation LibRelation LibOrder.
From TLC Require Export LibOrder.
Global Close Scope positive_scope.


(* ********************************************************************** *)
(** * Nat type *)

(* ---------------------------------------------------------------------- *)
(** ** Definition *)

(** From the Prelude:

  Inductive nat : Set :=
    | O : nat
    | S : nat -> nat.

  Remark: ideally, constructors would be renamed to [zero] and [succ],
  or [nat_zero] and [nat_succ], with the notations
  [O] or [0%nat], and [S n] or [succ n].
  It is indeed proablematic to prevent the use of single letter
  variables in pattern matching to the user who does not care about [nat].

*)

(* ---------------------------------------------------------------------- *)
(** ** Inhabited *)

#[global]
Instance Inhab_nat : Inhab nat.
Proof using. intros. apply (Inhab_of_val 0). Qed.



(* ********************************************************************** *)
(** * Order on natural numbers *)

(* ---------------------------------------------------------------------- *)
(** ** Definition *)

(** The typeclass instance of [le] on [nat] is defined to be the [le]
    relation on Peano numbers from Coq's standard library. *)

#[global]
Instance le_nat_inst : Le nat := Build_Le Peano.le.


(* ---------------------------------------------------------------------- *)
(** ** Translating typeclass instances to Peano relations *)

(** These lemmas and tactics are useful to transform arithmetic goals
    into a form on which the [lia] decision procedure may apply. *)

Lemma le_peano : le = Peano.le.
Proof using. extens*. Qed.

Global Opaque le_nat_inst.

Lemma lt_peano : lt = Peano.lt.
Proof using.
  extens. rew_to_le. rewrite le_peano.
  unfold strict. intros. lia.
Qed.

Lemma ge_peano : ge = Peano.ge.
Proof using.
  extens. rew_to_le. rewrite le_peano.
  unfold inverse. intros. lia.
Qed.

Lemma gt_peano : gt = Peano.gt.
Proof using.
  extens. rew_to_le. rewrite le_peano.
  unfold strict, inverse. intros. lia.
Qed.

#[global]
Hint Rewrite le_peano lt_peano ge_peano gt_peano : rew_nat_comp.

Ltac nat_comp_to_peano :=
  autorewrite with rew_nat_comp in *.

(** [nat_math] calls [lia] after basic pre-processing
    ([intros] and [split]) and after replacing comparison
    operators with the ones defined in [Peano] library. *)

Ltac nat_math_setup :=
  intros;
  try match goal with |- _ /\ _ => split end;
  try match goal with |- _ = _ :> Prop => apply prop_ext; iff end;
  nat_comp_to_peano.

Ltac nat_math :=
  nat_math_setup; lia.


(* ---------------------------------------------------------------------- *)
(** ** The [nat_maths] database is used for registering automation
       on mathematical goals. *)

(* --TODO: rename [nat_maths] database to [nat_math] *)

Ltac nat_math_hint := nat_math.

#[global]
Hint Extern 3 (_ = _ :> nat) => nat_math_hint : nat_maths.
#[global]
Hint Extern 3 (_ <> _ :> nat) => nat_math_hint : nat_maths.
#[global]
Hint Extern 3 (istrue (isTrue (_ = _ :> nat))) => nat_math_hint : nat_maths.
#[global]
Hint Extern 3 (istrue (isTrue (_ <> _ :> nat))) => nat_math_hint : nat_maths.
#[global]
Hint Extern 3 ((_ <= _)%nat) => nat_math_hint : nat_maths.
#[global]
Hint Extern 3 ((_ >= _)%nat) => nat_math_hint : nat_maths.
#[global]
Hint Extern 3 ((_ < _)%nat) => nat_math_hint : nat_maths.
#[global]
Hint Extern 3 ((_ > _)%nat) => nat_math_hint : nat_maths.
#[global]
Hint Extern 3 (@le nat _ _ _) => nat_math_hint : nat_maths.
#[global]
Hint Extern 3 (@lt nat _ _ _) => nat_math_hint : nat_maths.
#[global]
Hint Extern 3 (@ge nat _ _ _) => nat_math_hint : nat_maths.
#[global]
Hint Extern 3 (@gt nat _ _ _) => nat_math_hint : nat_maths.


(* ---------------------------------------------------------------------- *)
(** ** Total order instance *)

#[global]
Instance nat_le_total_order : Le_total_order (A:=nat).
Proof using.
  constructor. constructor. constructor; unfolds.
  nat_math. nat_math. nat_math.
  unfolds. intros. tests: (x <= y). left~. right. nat_math.
Qed.


(* ********************************************************************** *)
(** * Induction *)

Lemma peano_induction :
  forall (P:nat->Prop),
    (forall n, (forall m, m < n -> P m) -> P n) ->
    (forall n, P n).
Proof using.
  introv H. cuts* K: (forall n m, m < n -> P m).
  nat_comp_to_peano.
  induction n; introv Le. inversion Le. apply H.
  intros. apply IHn. nat_math.
Qed.

Lemma measure_induction :
  forall (A:Type) (mu:A->nat) (P:A->Prop),
    (forall x, (forall y, mu y < mu x -> P y) -> P x) ->
    (forall x, P x).
Proof using.
  introv IH. intros x. gen_eq n: (mu x). gen x.
  induction n using peano_induction. introv Eq. subst*.
Qed.


(* ********************************************************************** *)
(** * Simplification lemmas *)

(* ---------------------------------------------------------------------- *)
(** ** Trivial monoid simplifications *)

Lemma plus_zero_r : forall n,
  n + 0 = n.
Proof using. nat_math. Qed.

Lemma plus_zero_l : forall n,
  0 + n = n.
Proof using. nat_math. Qed.

Lemma minus_zero_r : forall n,
  n - 0 = n.
Proof using. nat_math. Qed.

Lemma plus_succ : forall n1 n2,
  n1 + S n2 = S (n1 + n2).
Proof using. nat_math. Qed.

Lemma minus_zero : forall n,
  n - 0 = n.
Proof using. nat_math. Qed.

Lemma succ_minus_succ : forall n1 n2,
  S n1 - S n2 = n1 - n2.
Proof using. nat_math. Qed.

Lemma minus_same : forall n,
  n - n = 0.
Proof using. nat_math. Qed.

Lemma plus_minus_same : forall n1 n2,
  n1 + n2 - n1 = n2.
Proof using. nat_math. Qed.

Lemma mult_zero_l : forall n,
  0 * n = 0.
Proof using. nat_math. Qed.

Lemma mult_zero_r : forall n,
  n * 0 = 0.
Proof using. nat_math. Qed.

Lemma mult_one_l : forall n,
  1 * n = n.
Proof using. nat_math. Qed.

Lemma mult_one_r : forall n,
  n * 1 = n.
Proof using. nat_math. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Simplification tactic *)

(** [rew_nat] performs some basic simplification on
    expressions involving natural numbers *)

#[global]
Hint Rewrite plus_zero_r plus_zero_l minus_zero_r
  plus_succ minus_zero succ_minus_succ minus_same plus_minus_same
  mult_zero_l mult_zero_r mult_one_l mult_one_r : rew_nat.

Tactic Notation "rew_nat" :=
  autorewrite with rew_nat.
Tactic Notation "rew_nat" "~" :=
  rew_nat; auto_tilde.
Tactic Notation "rew_nat" "*" :=
  rew_nat; auto_star.
Tactic Notation "rew_nat" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_nat).
  (* autorewrite with rew_nat in *. *)
Tactic Notation "rew_nat" "~" "in" "*" :=
  rew_nat in *; auto_tilde.
Tactic Notation "rew_nat" "*" "in" "*" :=
  rew_nat in *; auto_star.
Tactic Notation "rew_nat" "in" hyp(H) :=
  autorewrite with rew_nat in H.
Tactic Notation "rew_nat" "~" "in" hyp(H) :=
  rew_nat in H; auto_tilde.
Tactic Notation "rew_nat" "*" "in" hyp(H) :=
  rew_nat in H; auto_star.


(* ********************************************************************** *)
(** * Executable functions *)

Fixpoint beq (x y : nat) :=
  match x, y with
  | O, O => true
  | S x', S y' => beq x' y'
  | _, _ => false
  end.

Lemma beq_eq : forall n1 n2,
  beq n1 n2 = isTrue (n1 = n2).
Proof using.
  intros n1. induction n1; intros; destruct n2; simpl; rew_bool_eq; auto_false.
  rewrite IHn1. extens. rew_istrue. nat_math.
Qed.


(**************************************************************************
* TLC: A library for Coq                                                  *
* Naturals -- TODO: use typeclasses                                       *
**************************************************************************)

Set Implicit Arguments.
Require Export Arith Div2 Omega.
Require Import Psatz.
Require Import LibTactics LibReflect LibBool LibOperation LibRelation LibOrder.
Require Export LibOrder.
Global Close Scope positive_scope.

(* ********************************************************************** *)
(** * Inhabited and comparable *)

Instance nat_inhab : Inhab nat.
Proof using. intros. apply (prove_Inhab 0). Qed.

Fixpoint nat_compare (x y : nat) :=
  match x, y with
  | O, O => true
  | S x', S y' => nat_compare x' y'
  | _, _ => false
  end.

Instance nat_comparable : Comparable nat.
Proof using.
  applys (comparable_beq nat_compare).
  induction x; destruct y; simpl.
  autos*.
  auto_false.
  auto_false.
  asserts_rewrite ((S x = S y) = (x = y)).
    extens. iff; omega.
  autos*.
Qed.


(* ********************************************************************** *)
(** * Order on natural numbers *)

Instance le_nat_inst : Le nat := Build_Le Peano.le.

(* ---------------------------------------------------------------------- *)
(** ** Relation to Peano, for tactic [omega] *)

Lemma le_peano : le = Peano.le.
Proof using. extens*. Qed.

Global Opaque le_nat_inst.

Lemma lt_peano : lt = Peano.lt.
Proof using.
  extens. rew_to_le. rewrite le_peano.
  unfold strict. intros. omega.
Qed.

Lemma ge_peano : ge = Peano.ge.
Proof using.
  extens. rew_to_le. rewrite le_peano.
  unfold flip. intros. omega.
Qed.

Lemma gt_peano : gt = Peano.gt.
Proof using.
  extens. rew_to_le. rewrite le_peano.
  unfold strict, flip. intros. omega.
Qed.

Hint Rewrite le_peano lt_peano ge_peano gt_peano : rew_nat_comp.
Ltac nat_comp_to_peano :=
  autorewrite with rew_nat_comp in *.

(** [nat_math] calls [omega] after basic pre-processing
    ([intros] and [split]) and after replacing comparison
    operators with the ones defined in [Peano] library. *)

Ltac nat_math_setup :=
  intros;
  try match goal with |- _ /\ _ => split end;
  try match goal with |- _ = _ :> Prop => apply prop_ext; iff end;
  nat_comp_to_peano.

Ltac nat_math :=
  nat_math_setup; omega.

Ltac nat_math_lia :=
  nat_math_setup; lia.

Ltac nat_math_nia :=
  nat_math_setup; nia.

(* ---------------------------------------------------------------------- *)
(** ** Hint externs for calling nat_math{_lia,_nia} in the hint base
       [nat_maths]. *)

Ltac nat_math_hint := nat_math.

Hint Extern 3 (_ = _ :> nat) => nat_math_hint : nat_maths.
Hint Extern 3 (_ <> _ :> nat) => nat_math_hint : nat_maths.
Hint Extern 3 (istrue (isTrue (_ = _ :> nat))) => nat_math_hint : nat_maths.
Hint Extern 3 (istrue (isTrue (_ <> _ :> nat))) => nat_math_hint : nat_maths.
Hint Extern 3 (_ <= _) => nat_math_hint : nat_maths.
Hint Extern 3 (_ >= _) => nat_math_hint : nat_maths.
Hint Extern 3 (_ < _) => nat_math_hint : nat_maths.
Hint Extern 3 (_ > _) => nat_math_hint : nat_maths.
Hint Extern 3 (@le nat _ _ _) => nat_math_hint : nat_maths.
Hint Extern 3 (@lt nat _ _ _) => nat_math_hint : nat_maths.
Hint Extern 3 (@ge nat _ _ _) => nat_math_hint : nat_maths.
Hint Extern 3 (@gt nat _ _ _) => nat_math_hint : nat_maths.

(* ********************************************************************** *)
(** * Operations *)

Definition div (n q : nat) :=
  match q with
  | 0 => 0
  | S predq =>
  let aux := fix aux (m r : nat) {struct m} :=
    match m,r with
    | 0, _ => 0
    | S m',0 => (1 + aux m' predq)%nat
    | S m', S r' => aux m' r'
    end in
  aux n predq
  end.

Fixpoint factorial (n:nat) : nat :=
  match n with
  | 0 => 1
  | S n' => n * (factorial n')
  end.


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
(** ** Addition and substraction *)

Lemma plus_zero_r : forall n,
  n + 0 = n.
Proof using. nat_math. Qed.
Lemma plus_zero_l : forall n,
  0 + n = n.
Proof using. nat_math. Qed.
Lemma minus_zero : forall n,
  n - 0 = n.
Proof using. nat_math. Qed.

Hint Rewrite plus_zero_r plus_zero_l minus_zero : rew_nat.

(* ---------------------------------------------------------------------- *)
(** ** Comparison *)

Section CompProp.
Implicit Types a b c n m : nat.

Lemma le_SS : forall n m, (S n <= S m) = (n <= m).
Proof using. nat_math. Qed.
Lemma ge_SS : forall n m, (S n >= S m) = (n >= m).
Proof using. nat_math. Qed.
Lemma lt_SS : forall n m, (S n < S m) = (n < m).
Proof using. nat_math. Qed.
Lemma gt_SS : forall n m, (S n > S m) = (n > m).
Proof using. nat_math. Qed.

Lemma plus_le_l : forall a b c,
  (a + b <= a + c) = (b <= c).
Proof using. nat_math. Qed.
Lemma plus_ge_l : forall a b c,
  (a + b >= a + c) = (b >= c).
Proof using. nat_math. Qed.
Lemma plus_lt_l : forall a b c,
  (a + b < a + c) = (b < c).
Proof using. nat_math. Qed.
Lemma plus_gt_l : forall a b c,
  (a + b > a + c) = (b > c).
Proof using. nat_math. Qed.

Lemma plus_le_r : forall a b c,
  (b + a <= c + a) = (b <= c).
Proof using. nat_math. Qed.
Lemma plus_ge_r : forall a b c,
  (b + a >= c + a) = (b >= c).
Proof using. nat_math. Qed.
Lemma plus_lt_r : forall a b c,
  (b + a < c + a) = (b < c).
Proof using. nat_math. Qed.
Lemma plus_gt_r : forall a b c,
  (b + a > c + a) = (b > c).
Proof using. nat_math. Qed.

End CompProp.

(* todo: negation *)

(* ---------------------------------------------------------------------- *)
(** ** Simplification tactic *)

(** [rew_nat] performs some basic simplification on
    expressions involving natural numbers *)

Hint Rewrite le_SS ge_SS lt_SS gt_SS : rew_nat.
Hint Rewrite plus_le_l plus_ge_l plus_lt_l plus_gt_l : rew_nat.
Hint Rewrite plus_le_r plus_ge_r plus_lt_r plus_gt_r : rew_nat.

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


(* ---------------------------------------------------------------------- *)
(* Total order instance *)

Instance nat_le_total_order : Le_total_order (A:=nat).
Proof using.
  constructor. constructor. constructor; unfolds.
  nat_math. nat_math. unfolds. nat_math. unfolds.
  intros. tests: (x <= y). left~. right. nat_math.
Qed.

(* ********************************************************************** *)
(** * Other lemmas *)

(* ---------------------------------------------------------------------- *)
(** ** Div2 *)

Lemma div2_lt : forall n m, m <= n -> n > 0 -> div2 m < n.
Proof using. (* using stdlib *)
  nat_comp_to_peano. introv Le Gt.
  forwards: Nat.div2_decr m (n-1). omega. omega.
Qed.

Lemma div2_grows : forall n m, m <= n -> div2 m <= div2 n.
Proof using.
  nat_comp_to_peano.
  induction n using peano_induction. introv Le.
  destruct~ m. simpl. omega.
  destruct~ n. simpl. omega.
  destruct~ m. simpl. omega.
  destruct~ n. simpl. omega.
  simpl. rew_nat. apply~ H. nat_math. nat_math.
Qed.

(**************************************************************************
* TLC: A library for Coq                                                  *
* Integers                                                                *
**************************************************************************)

Set Implicit Arguments.
Require Export Coq.ZArith.ZArith.
From TLC Require Import LibTactics LibLogic LibReflect LibRelation.
Export LibTacticsCompatibility.
From TLC Require Export LibNat.

(* --LATER: rename [plus] to [add] everywhere? *)

(* ********************************************************************** *)
(** * Parsing of integers and operations *)

(* ---------------------------------------------------------------------- *)
(** ** Notation for type and operation *)

(** Define [int] as an alias for [Z], the type of integers from Coq's stdlib. *)

Declare Scope Int_scope.
Notation "'int'" := Z : Int_scope.
Delimit Scope Int_scope with I.

Local Open Scope Int_scope.


(* ---------------------------------------------------------------------- *)
(** ** Inhabited type *)

#[global]
Instance Inhab_int : Inhab int.
Proof using. intros. apply (Inhab_of_val 0%Z). Qed.


(* ---------------------------------------------------------------------- *)
(** ** Coercion from nat *)

(** Remark: we cannot simply use the coercion:
      Coercion Z_of_nat : nat >-> Z.
   because otherwise when we try to make the coercion opaque using:
      Opaque Z_of_nat.
   the lia fails to work.
   Thus, we introduce an alias, called [nat_to_Z] for [Z_of_nat],
   and we register [nat_to_Z] as coercion.
*)

Definition nat_to_Z := Z_of_nat.

Lemma nat_to_Z_eq_Z_of_nat : nat_to_Z = Z_of_nat.
Proof using. reflexivity. Qed.

Global Opaque nat_to_Z.

Coercion nat_to_Z : nat >-> Z.

(* --TODO: check this coercion is actually the one in use *)


(* ---------------------------------------------------------------------- *)
(** ** Order relation *)

(** The comparison operators on integers are those from [LibOrder],
    not the ones from Coq's [ZArith]. *)

Open Scope Z_scope.
Open Scope comp_scope.

(** The typeclass [le] on type [int] is bound to [Zle], from Coq's
    standard library *)

#[global]
Instance le_int_inst : Le int := Build_Le Z.le.



(* ********************************************************************** *)
(** * Conversion to natural numbers, for tactic programming *)

(** These tactics are helpful to convert a number passed to a Ltac tactic
    into a [nat], regardless of whether it is a [nat] or an [int]. *)

Definition ltac_int_to_nat (x:Z) : nat :=
  match x with
  | Z0 => 0%nat
  | Zpos p => nat_of_P p
  | Zneg p => 0%nat
  end.

Ltac number_to_nat N ::=
  match type of N with
  | nat => constr:(N)
  | int => let N' := constr:(ltac_int_to_nat N) in eval compute in N'
  | Z => let N' := constr:(ltac_int_to_nat N) in eval compute in N'
  (*todo: last case not needed*)
  end.



(* ********************************************************************** *)
(** * Decision procedure *)

(** A lot of hacks to allow calling the [lia] tactic *)

(* ---------------------------------------------------------------------- *)
(** ** Translation from typeclass order to ZArith, for using [lia] *)

Lemma le_zarith : le = Z.le.
Proof using. extens*. Qed.

Global Opaque le_int_inst.

Lemma lt_zarith : lt = Z.lt.
Proof using.
  extens. rew_to_le. rewrite le_zarith.
  unfold strict. intros. lia.
Qed.

Lemma ge_zarith : ge = Z.ge.
Proof using.
  extens. rew_to_le. rewrite le_zarith.
  unfold inverse. intros. lia.
Qed.

Lemma gt_zarith : gt = Z.gt.
Proof using.
  extens. rew_to_le. rewrite le_zarith.
  unfold strict, inverse. intros. lia.
Qed.

#[global]
Hint Rewrite le_zarith lt_zarith ge_zarith gt_zarith : rew_int_comp.

Ltac int_comp_to_zarith :=
  autorewrite with rew_int_comp in *.

(* ---------------------------------------------------------------------- *)
(** ** Hypothesis selection *)

(** [is_additional_arith_type T] allows for extending the behavior of
    [is_arith_type]. *)

Ltac is_additional_arith_type T :=
  constr:(false).

(** [is_arity_type T] returns a boolean indicating whether
    [T] is equal to [nat] or [int] *)

Ltac is_arith_type T :=
  match T with
  | nat => constr:(true)
  | int => constr:(true)
  | _ => is_additional_arith_type T
  end.

(** [is_arity E] returns a boolean indicating whether
    [E] is an arithmetic expression *)

Ltac is_arith E :=
  match E with
  | _ = _ :> ?T => is_arith_type T
  | _ <> _ :> ?T => is_arith_type T
  | ~ ?E' => is_arith E'
  | ?E' -> False => is_arith E'
  | @le ?T _ _ _ => is_arith_type T
  | @ge ?T _ _ _ => is_arith_type T
  | @lt ?T _ _ _ => is_arith_type T
  | @gt ?T _ _ _ => is_arith_type T
  | (_ <= _)%Z => constr:(true)
  | (_ >= _)%Z => constr:(true)
  | (_ < _)%Z => constr:(true)
  | (_ > _)%Z => constr:(true)
  | (_ <= _)%nat => constr:(true)
  | (_ >= _)%nat => constr:(true)
  | (_ < _)%nat => constr:(true)
  | (_ > _)%nat => constr:(true)
  | _ => constr:(false)
  end.

(** [arith_goal_or_false] looks at the current goal and
    replaces it with [False] if it is not an arithmetic goal*)

Ltac arith_goal_or_false :=
  match goal with |- ?E =>
    match is_arith E with
    | true => idtac
    | false => false
    end
  end.

(** [generalize_arith] generalizes all hypotheses which correspond
    to some arithmetic goal. It destructs conjunctions on the fly. *)

Lemma istrue_isTrue_forw : forall (P:Prop),
  istrue (isTrue P) ->
  P.
Proof using. introv H. rew_istrue~ in H. Qed.

Ltac generalize_arith :=
  repeat match goal with
  | H: istrue (isTrue _) |- _ => generalize (@istrue_isTrue_forw _ H); clear H; intro
  | H:?E1 /\ ?E2 |- _ => destruct H
  | H: ?E -> False |- _ =>
    match is_arith E with
    | true => change (E -> False) with (~ E) in H
    | false => clear H
    end
  | H:?E |- _ =>
    match is_arith E with
    | true => generalize H; clear H (* --todo: revert H? *)
    | false => clear H
    end
  end.

(* --TODO:
Ltac split_if_eq_bool :=
  let go _ := apply eq_bool_prove; intros in
  match goal with
  | |- @eq bool _ _ => go tt
  | |- istrue (@eqb bool _ _ _) => apply eq_to_equ; go tt
  end.
*)

(* ---------------------------------------------------------------------- *)
(** ** Normalization of arithmetic expressions *)

(** Two lemmas to help lia out *)

Lemma Z_of_nat_O :
  Z_of_nat O = 0.
Proof using. reflexivity. Qed.

Lemma Z_of_nat_S : forall n,
  Z_of_nat (S n) = Z.succ (Z_of_nat n).
Proof using. intros. rewrite~ <- Zpos_P_of_succ_nat. Qed.

Lemma Z_of_nat_plus1 : forall n,
  Z_of_nat (1 + n) = Z.succ (Z_of_nat n).
Proof using. intros. rewrite <- Z_of_nat_S. fequals~. Qed.

(** [rew_maths] rewrite any lemma in the base [rew_maths].
    The goal should not contain any evar, otherwise tactic might loop. *)

#[global]
Hint Rewrite nat_to_Z_eq_Z_of_nat Z_of_nat_O Z_of_nat_S Z_of_nat_plus1 : rew_maths.

Ltac rew_maths :=
  autorewrite with rew_maths in *.


(* ---------------------------------------------------------------------- *)
(** ** Setting up the goal for [lia] *)

(** [math_setup_goal] does introduction, splits, and replace
    the goal by [False] if it is not arithmetic. If the goal
    is of the form [P1 = P2 :> Prop], then the goal is
    changed to [P1 <-> P2]. *)

Ltac math_setup_goal_step tt :=
  match goal with
  | |- _ -> _ => intro
  | |- _ <-> _ => iff
  | |- forall _, _  => intro
  | |- _ /\ _ => split
  | |- _ = _ :> Prop => apply prop_ext; iff
  end.

Ltac math_setup_goal :=
  repeat (math_setup_goal_step tt);
  arith_goal_or_false.

  (* DEPRECATED
  Ltac math_setup_goal :=
    intros;
    try match goal with |- _ /\ _ => split end;
    try match goal with |- _ = _ :> Prop => apply prop_ext; iff end;
    arith_goal_or_false.
    (* try split_if_eq_bool. *)
  *)

(* --TODO; [int_nat_conv]
Lemma int_nat_plus : forall (n m:nat),
  (n + m)%nat = (n + m)%Z :> int.
Proof using. applys inj_plus. Qed.
Hint Rewrite int_nat_plus : int_nat_conv.
*)

(** [math] tactics performs several preprocessing step,
    selects all arithmetic hypotheses, and the call lia. *)
(* --TODO: autorewrite with int_nat_conv in *. after int_comp_to_zarith *)


(* ---------------------------------------------------------------------- *)
(** ** Main driver for the set up process to goal [lia] *)

(* --TODO: this probably is no longer necessary, since
     LibTactic version seems equivalent *)
Ltac check_noevar_goal ::=
  match goal with |- ?G => first [ has_evar G; fail 1 | idtac ] end.

Ltac math_0 := idtac.
Ltac math_1 := intros; generalize_arith.
(* Work around for the slow [autorewrite in *] *)
Ltac math_2 := check_noevar_goal.
Ltac math_3 := autorewrite with rew_maths rew_int_comp rew_nat_comp; intros.
(* original:
Ltac math_2 := instantiate; check_noevar_goal; intros.
Ltac math_3 := rew_maths; nat_comp_to_peano; int_comp_to_zarith.
*)
Ltac math_4 := math_setup_goal.
Ltac math_5 := lia.

Ltac math_setup := math_0; math_1; math_2; math_3; math_4.
Ltac math_base := math_setup; math_5.

Tactic Notation "math" := math_base.

Tactic Notation "math" simple_intropattern(I) ":" constr(E) :=
  asserts I: E; [ math | ].
Tactic Notation "maths" constr(E) :=
  let H := fresh "H" in asserts H: E; [ math | ].
(* --TODO: parsing conflit *)


(* ---------------------------------------------------------------------- *)
(** ** [math] tactic restricted to arithmetic goals *)

(** [math_only] calls [math] but only on goals which
    have an arithmetic form. Thus, contracty to [math],
    it does not attempt to look for a contradiction in
    the hypotheses if the conclusion is not an arithmetic
    goal. Useful for efficiency. *)

Ltac math_only_if_arith_core tt :=
  match goal with |- ?T =>
    match is_arith T with true => math end end.

Tactic Notation "math_only_if_arith" :=
  math_only_if_arith_core tt.


(* ---------------------------------------------------------------------- *)
(** ** Elimination of multiplication, to call lia *)

(* In order to use [math] with simple multiplications, add the command:
     Hint Rewrite mult_2_eq_plus mult_3_eq_plus : rew_maths.
   TEMPORARY: these lemmas should go away as [lia] is able to inline
   trivial multiplication by itself
*)

Lemma mult_2_eq_plus : forall x, 2 * x = x + x.
Proof using. intros. ring. Qed.

Lemma mult_3_eq_plus : forall x, 3 * x = x + x + x.
Proof using. intros. ring. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Hint externs for calling math in the hint base [maths] *)

(* --TODO: rename [maths] database to [math] *)

Ltac math_hint := math.

#[global]
Hint Extern 3 (_ = _ :> nat) => math_hint : maths.
#[global]
Hint Extern 3 (_ = _ :> int) => math_hint : maths.
#[global]
Hint Extern 3 (_ <> _ :> nat) => math_hint : maths.
#[global]
Hint Extern 3 (_ <> _ :> int) => math_hint : maths.
#[global]
Hint Extern 3 (istrue (isTrue (_ = _ :> nat))) => math_hint : maths.
#[global]
Hint Extern 3 (istrue (isTrue (_ = _ :> int))) => math_hint : maths.
#[global]
Hint Extern 3 (istrue (isTrue (_ <> _ :> nat))) => math_hint : maths.
#[global]
Hint Extern 3 (istrue (isTrue (_ <> _ :> int))) => math_hint : maths.
#[global]
Hint Extern 3 ((_ <= _)%nat) => math_hint : maths.
#[global]
Hint Extern 3 ((_ >= _)%nat) => math_hint : maths.
#[global]
Hint Extern 3 ((_ < _)%nat) => math_hint : maths.
#[global]
Hint Extern 3 ((_ > _)%nat) => math_hint : maths.
#[global]
Hint Extern 3 ((_ <= _)%Z) => math_hint : maths.
#[global]
Hint Extern 3 ((_ >= _)%Z) => math_hint : maths.
#[global]
Hint Extern 3 ((_ < _)%Z) => math_hint : maths.
#[global]
Hint Extern 3 ((_ > _)%Z) => math_hint : maths.
#[global]
Hint Extern 3 (@le nat _ _ _) => math_hint : maths.
#[global]
Hint Extern 3 (@lt nat _ _ _) => math_hint : maths.
#[global]
Hint Extern 3 (@ge nat _ _ _) => math_hint : maths.
#[global]
Hint Extern 3 (@gt nat _ _ _) => math_hint : maths.
#[global]
Hint Extern 3 (@le int _ _ _) => math_hint : maths.
#[global]
Hint Extern 3 (@lt int _ _ _) => math_hint : maths.
#[global]
Hint Extern 3 (@ge int _ _ _) => math_hint : maths.
#[global]
Hint Extern 3 (@gt int _ _ _) => math_hint : maths.
#[global]
Hint Extern 3 (~ @le int _ _ _) => unfold not; math_hint : maths.
#[global]
Hint Extern 3 (~ @lt int _ _ _) => unfold not; math_hint : maths.
#[global]
Hint Extern 3 (~ @ge int _ _ _) => unfold not; math_hint : maths.
#[global]
Hint Extern 3 (~ @gt int _ _ _) => unfold not; math_hint : maths.
#[global]
Hint Extern 3 (~ @eq int _ _) => unfold not; math_hint : maths.
#[global]
Hint Extern 3 (@le int _ _ _ -> False) => math_hint : maths.
#[global]
Hint Extern 3 (@lt int _ _ _ -> False) => math_hint : maths.
#[global]
Hint Extern 3 (@ge int _ _ _ -> False) => math_hint : maths.
#[global]
Hint Extern 3 (@gt int _ _ _ -> False) => math_hint : maths.
#[global]
Hint Extern 3 (@eq int _ _ -> False) => math_hint : maths.
#[global]
Hint Extern 3 (~ @le nat _ _ _) => unfold not; math_hint : maths.
#[global]
Hint Extern 3 (~ @lt nat _ _ _) => unfold not; math_hint : maths.
#[global]
Hint Extern 3 (~ @ge nat _ _ _) => unfold not; math_hint : maths.
#[global]
Hint Extern 3 (~ @gt nat _ _ _) => unfold not; math_hint : maths.
#[global]
Hint Extern 3 (~ @eq nat _ _) => unfold not; math_hint : maths.
#[global]
Hint Extern 3 (@le nat _ _ _ -> False) => math_hint : maths.
#[global]
Hint Extern 3 (@lt nat _ _ _ -> False) => math_hint : maths.
#[global]
Hint Extern 3 (@ge nat _ _ _ -> False) => math_hint : maths.
#[global]
Hint Extern 3 (@gt nat _ _ _ -> False) => math_hint : maths.
#[global]
Hint Extern 3 (@eq nat _ _ -> False) => math_hint : maths.


(* ********************************************************************** *)
(** * Rewriting on arithmetic expressions *)

(* ---------------------------------------------------------------------- *)
(** ** Rewriting equalities provable by the [math] tactic *)

(** [math_rewrite (E = F)] replaces all occurences of [E]
    with the expression [F]. It produces the equality [E = F]
    as subgoal, and tries to solve it using the tactic [math] *)

Tactic Notation "math_rewrite" constr(E) :=
  asserts_rewrite E; [ try math | ].
Tactic Notation "math_rewrite" constr(E) "in" hyp(H) :=
  asserts_rewrite E in H; [ try math | ].
Tactic Notation "math_rewrite" constr(E) "in" "*" :=
  asserts_rewrite E in *; [ try math | ].

Tactic Notation "math_rewrite" "~" constr(E) :=
  math_rewrite E; auto_tilde.
Tactic Notation "math_rewrite" "~" constr(E) "in" hyp(H) :=
  math_rewrite E in H; auto_tilde.
Tactic Notation "math_rewrite" "~" constr(E) "in" "*" :=
  math_rewrite E in *; auto_tilde.

Tactic Notation "math_rewrite" "*" constr(E) :=
  math_rewrite E; auto_star.
Tactic Notation "math_rewrite" "*" constr(E) "in" hyp(H) :=
  math_rewrite E in H; auto_star.
Tactic Notation "math_rewrite" "*" constr(E) "in" "*" :=
  math_rewrite E in *; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** Addition and substraction *)

Lemma plus_zero_r : forall n,
  n + 0 = n.
Proof using. math. Qed.

Lemma plus_zero_l : forall n,
  0 + n = n.
Proof using. math. Qed.

Lemma minus_zero_r : forall n,
  n - 0 = n.
Proof using. math. Qed.

Lemma minus_zero_l : forall n,
  0 - n = (-n).
Proof using. math. Qed.

Lemma mult_zero_l : forall n,
  0 * n = 0.
Proof using. math. Qed.

Lemma mult_zero_r : forall n,
  n * 0 = 0.
Proof using. math. Qed.

Lemma mult_one_l : forall n,
  1 * n = n.
Proof using. math. Qed.

Lemma mult_one_r : forall n,
  n * 1 = n.
Proof using. math. Qed.

Lemma minus_self : forall n,
  n - n = 0.
Proof using. math. Qed.

Lemma one_plus_minus_one_r : forall n,
  1 + (n - 1) = n.
Proof using. math. Qed.

Lemma plus_one_minus_one_l : forall n,
  (n + 1) - 1 = n.
Proof using. math. Qed.

Lemma one_plus_minus_one_l : forall n,
  (1 + n) - 1 = n.
Proof using. math. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Simplification tactic *)

(** [rew_int] performs some basic simplification on
    expressions involving integers *)

#[global]
Hint Rewrite plus_zero_r plus_zero_l minus_zero_r minus_zero_l
  mult_zero_l mult_zero_r mult_one_l mult_one_r
  minus_self one_plus_minus_one_r plus_one_minus_one_l
  one_plus_minus_one_l : rew_int.

Tactic Notation "rew_int" :=
  autorewrite with rew_int.
Tactic Notation "rew_int" "~" :=
  rew_int; auto_tilde.
Tactic Notation "rew_int" "*" :=
  rew_int; auto_star.
Tactic Notation "rew_int" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_int).
  (* autorewrite with rew_int in *. *)
Tactic Notation "rew_int" "~" "in" "*" :=
  rew_int in *; auto_tilde.
Tactic Notation "rew_int" "*" "in" "*" :=
  rew_int in *; auto_star.
Tactic Notation "rew_int" "in" hyp(H) :=
  autorewrite with rew_int in H.
Tactic Notation "rew_int" "~" "in" hyp(H) :=
  rew_int in H; auto_tilde.
Tactic Notation "rew_int" "*" "in" hyp(H) :=
  rew_int in H; auto_star.


(* ********************************************************************** *)
(** * Conversions of operations from [nat] to [int] and back *)

(** -- LATER: make proofs below no longer depend on Coq's stdlib *)

(* ---------------------------------------------------------------------- *)
(** ** Lifting of comparisons from [nat] to [int] *)

(* --TODO: perhaps only state those as equalities? *)

Lemma eq_nat_of_eq_int : forall (n m:nat),
  (n:int) = (m:int) ->
  n = m :> nat.
Proof using. math. Qed.

Lemma neq_nat_of_neq_int : forall (n m:nat),
  (n:int) <> (m:int) ->
  (n <> m)%nat.
Proof using. math. Qed.

Lemma eq_int_of_eq_nat : forall (n m:nat),
  n = m :> nat ->
  (n:int) = (m:int).
Proof using. math. Qed.

Lemma neq_int_of_neq_nat : forall (n m:nat),
  (n <> m)%nat ->
  (n:int) <> (m:int).
Proof using. math. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Lifting of inequalities from [nat] to [int] *)

Lemma le_nat_of_le_int : forall (n m:nat),
  (n:int) <= (m:int) ->
  (n <= m).
Proof using. math. Qed.

Lemma le_int_of_le_nat : forall (n m:nat),
  (n <= m) ->
  (n:int) <= (m:int).
Proof using. math. Qed.

Lemma lt_nat_of_lt_int : forall (n m:nat),
  (n:int) < (m:int) ->
  (n < m).
Proof using. math. Qed.

Lemma lt_int_of_lt_nat : forall (n m:nat),
  (n < m) ->
  (n:int) < (m:int).
Proof using. math. Qed.

Lemma ge_nat_of_ge_int : forall (n m:nat),
  (n:int) >= (m:int) ->
  (n >= m).
Proof using. math. Qed.

Lemma ge_int_of_ge_nat : forall (n m:nat),
  (n >= m) ->
  (n:int) >= (m:int).
Proof using. math. Qed.

Lemma gt_nat_of_gt_int : forall (n m:nat),
  (n:int) > (m:int) ->
  (n > m).
Proof using. math. Qed.

Lemma gt_int_of_gt_nat : forall (n m:nat),
  (n > m) ->
  (n:int) > (m:int).
Proof using. math. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Lifting of operations from [nat] to [int] *)

Lemma plus_nat_eq_plus_int : forall (n m:nat),
  (n+m)%nat = (n:int) + (m:int) :> int.
Proof using.
  Transparent nat_to_Z.
  intros. unfold nat_to_Z. applys Nat2Z.inj_add.
Qed.

Lemma minus_nat_eq_minus_int : forall (n m:nat),
  (n >= m)%nat ->
  (n-m)%nat = (n:int) - (m:int) :> int.
Proof using.
  Transparent nat_to_Z.
  intros. unfold nat_to_Z. applys Nat2Z.inj_sub. math.
Qed.

(* -- LATER: tactic for lifting all operators and comparisons into Z *)

(* -- LATER: complete with other operators *)

(* -- LATER: is the hint below really necessary?
     if so, there should probably be other hints similar to it *)

#[global]
Hint Rewrite plus_nat_eq_plus_int : rew_maths.


(* ---------------------------------------------------------------------- *)
(** ** Properties of comparison *)

Lemma antisym_le_int :
  antisym (le (A:=int)).
Proof using. intros x y L1 L2. math. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Absolute function in [nat] *)

Notation "'abs'" := Z.abs_nat (at level 0).

Global Arguments Z.abs : simpl never.
Global Arguments Z.abs_nat : simpl never.

Lemma abs_nat : forall (n:nat),
  abs n = n.
Proof using. exact Zabs_nat_Z_of_nat. Qed.

Lemma abs_nonneg : forall (x:int),
  x >= 0 ->
  abs x = x :> int.
Proof using.
  intros. rewrite inj_Zabs_nat.
  rewrite Z.abs_eq. math. math.
Qed.

Lemma abs_eq_nat_eq : forall (x:int) (y:nat),
  x >= 0 ->
  (abs x = y :> nat) = (x = Z_of_nat y :> int).
Proof using.
  introv M. extens. iff E.
  { subst. rewrite Zabs2Nat.id_abs, Z.abs_eq; math. }
  { subst. rewrite~ Zabs2Nat.id. }
Qed.

Lemma lt_abs_abs : forall (n m : int),
  (0 <= n) ->
  (n < m) ->
  (abs n < abs m).
Proof using.
  intros. nat_comp_to_peano. apply Zabs_nat_lt. math.
Qed.

Lemma abs_to_int : forall (n : int),
  0 <= n ->
  Z_of_nat (abs n) = n.
Proof using. intros. rewrite~ abs_nonneg. Qed.

Lemma abs_le_nat_le : forall (x:int) (y:nat),
  (0 <= x) ->
  (abs x <= y) = (x <= y)%Z.
Proof.
  intros. extens. iff E.
  { rewrites~ <-(>> abs_to_int x). math. }
  { rewrites~ <-(>> abs_to_int x) in E. math. }
Qed.

Lemma abs_ge_nat_ge : forall (x:int) (y:nat),
  (0 <= x) ->
  (abs x >= y) = (x >= y)%Z .
Proof.
  intros. extens. iff E.
  { rewrites~ <-(>> abs_to_int x). math. }
  { rewrites~ <-(>> abs_to_int x) in E. math. }
Qed.

(** -- TODO: many useful lemmas missing *)


(* ---------------------------------------------------------------------- *)
(** ** [abs] distribute on constants and operators *)

Lemma abs_0 : abs 0 = 0%nat :> nat.
Proof using. reflexivity. Qed.

Lemma abs_1 : abs 1 = 1%nat :> nat.
Proof using. reflexivity. Qed.

Lemma abs_plus : forall (x y:int),
  (x >= 0) ->
  (y >= 0) ->
  abs (x + y) = (abs x + abs y)%nat :> nat.
Proof using. intros. applys Zabs2Nat.inj_add; math. Qed.

Lemma abs_minus : forall (x y:int),
  (x >= y) ->
  (y >= 0) ->
  abs (x - y) = (abs x - abs y)%nat :> nat.
Proof using. intros. applys Zabs2Nat.inj_sub; math. Qed.

Lemma abs_nat_plus_nonneg : forall (n:nat) (x:int),
  x >= 0 ->
 abs (n + x)%Z = (n + abs x)%nat.
Proof using.
  introv N. applys eq_nat_of_eq_int.
  rewrite plus_nat_eq_plus_int.
  do 2 (rewrite abs_nonneg; [|math]). auto.
Qed.

Lemma abs_gt_minus_nat : forall (n:nat) (x:int),
  (x >= n)%Z ->
 abs (x - n)%Z = (abs x - n)%nat.
Proof using.
  introv N. applys eq_nat_of_eq_int.
  rewrite minus_nat_eq_minus_int.
  do 2 (rewrite abs_nonneg; [|math]). auto.
  applys ge_nat_of_ge_int. rewrite abs_nonneg; math.
Qed.

Lemma succ_abs_eq_abs_one_plus : forall (x:int),
  x >= 0 ->
  S (abs x) = abs (1 + x) :> nat.
Proof using.
  intros x. pattern x. applys (@measure_induction _ abs). clear x.
  intros x IH Pos. rewrite <- Zabs_nat_Zsucc. fequals. math. math.
Qed.

Lemma abs_eq_succ_abs_minus_one : forall (x:int),
  x > 0 ->
  abs x = S (abs (x - 1)) :> nat.
Proof using.
  intros. apply eq_nat_of_eq_int.
  rewrite abs_nonneg; try math.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [rew_abs_nonneg] to normalize expressions involving [abs]
       issuing side-conditions that arguments are nonnegative *)

#[global]
Hint Rewrite abs_nat abs_0 abs_1 abs_plus abs_nonneg : rew_abs_nonneg.

Tactic Notation "rew_abs_nonneg" :=
  autorewrite with rew_abs_nonneg.
Tactic Notation "rew_abs_nonneg" "~" :=
  autorewrite with rew_abs_nonneg; try math; autos~.


(* ---------------------------------------------------------------------- *)
(** ** Positive part of an integer. Returns 0 on negative values. *)

Notation "'to_nat'" := Z.to_nat (at level 0).

Lemma to_nat_nat : forall (n:nat),
  to_nat n = n.
Proof using. exact Nat2Z.id. Qed.

Lemma to_nat_nonneg : forall (x:int),
  x >= 0 ->
  to_nat x = x :> int.
Proof using. intros. apply~ Z2Nat.id. Qed.

Lemma to_nat_neg : forall (x:int),
  x <= 0 ->
  to_nat x = 0%nat.
Proof using.
  intros x H. destruct~ x.
  assert (Z.pos p = 0) as ->. { forwards: Zle_0_pos p. math. }
  reflexivity.
Qed.

Lemma to_nat_eq_nat_eq : forall (x:int) (y:nat),
  x >= 0 ->
  (to_nat x = y :> nat) = (x = Z_of_nat y :> int).
Proof using.
  introv M. extens. iff E.
  { subst. rewrite~ Z2Nat.id. }
  { subst. rewrite~ Nat2Z.id. }
Qed.

Lemma lt_to_nat_to_nat : forall (n m : int),
  (0 <= n) ->
  (n < m) ->
  (to_nat n < to_nat m).
Proof using.
  intros. nat_comp_to_peano.
  rewrite <-!Zabs2Nat.abs_nat_nonneg by math.
  apply~ Zabs_nat_lt. math.
Qed.

Lemma to_nat_to_int : forall (n : int),
  0 <= n ->
  Z_of_nat (to_nat n) = n.
Proof using. intros. rewrite~ to_nat_nonneg. Qed.

Lemma to_nat_le_nat_le : forall (x:int) (y:nat),
  (0 <= x) ->
  (to_nat x <= y) = (x <= y)%Z.
Proof.
  intros. extens. iff E.
  { rewrites~ <-(>> to_nat_to_int x). math. }
  { rewrites~ <-(>> to_nat_to_int x) in E. math. }
Qed.

Lemma to_nat_ge_nat_ge : forall (x:int) (y:nat),
  (0 <= x) ->
  (to_nat x >= y) = (x >= y)%Z .
Proof.
  intros. extens. iff E.
  { rewrites~ <-(>> to_nat_to_int x). math. }
  { rewrites~ <-(>> to_nat_to_int x) in E. math. }
Qed.

(* ---------------------------------------------------------------------- *)
(** ** [to_nat] distribute on constants and operators *)

Lemma to_nat_0 : to_nat 0 = 0%nat :> nat.
Proof using. reflexivity. Qed.

Lemma to_nat_1 : to_nat 1 = 1%nat :> nat.
Proof using. reflexivity. Qed.

Lemma to_nat_plus : forall (x y:int),
  (x >= 0) ->
  (y >= 0) ->
  to_nat (x + y) = (to_nat x + to_nat y)%nat :> nat.
Proof using. intros. apply~ Z2Nat.inj_add. Qed.

Lemma to_nat_minus : forall (x y:int),
  (x >= y) ->
  (y >= 0) ->
  to_nat (x - y) = (to_nat x - to_nat y)%nat :> nat.
Proof using. intros. apply~ Z2Nat.inj_sub. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [rew_to_nat_nonneg] to normalize expressions involving [to_nat]
       issuing side-conditions that arguments are nonnegative *)

#[global]
Hint Rewrite to_nat_nat to_nat_0 to_nat_1 to_nat_plus to_nat_minus
     to_nat_nonneg : rew_to_nat_nonneg.

Tactic Notation "rew_to_nat_nonneg" :=
  autorewrite with rew_to_nat_nonneg.
Tactic Notation "rew_to_nat_nonneg" "~" :=
  autorewrite with rew_to_nat_nonneg; try math; autos~.

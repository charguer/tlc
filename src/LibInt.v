(**************************************************************************
* TLC: A library for Coq                                                  *
* Integers -- TODO: use typeclasses                                       *
**************************************************************************)

Set Implicit Arguments.
Require Export ZArith.
Require Import LibTactics LibLogic LibReflect LibRelation.
Require Import Psatz.
Export LibTacticsCompatibility.
Require Export LibNat.

(* ********************************************************************** *)
(** * Notation for integers *)

(* Comparison operators are those of LibOrder, not ZArith *)

Open Scope Z_scope.
Open Scope comp_scope.

Notation "'int'" := Z : Int_scope.

Infix "+" := Zplus : Int_scope.
Notation "- x" := (Zopp x) : Int_scope.
Infix "-" := Zminus : Int_scope.
Infix "*" := Zmult : Int_scope.

Bind Scope Int_scope with Z.
Delimit Scope Int_scope with I.
Open Scope Int_scope.

(* todo: is all of this really necessary ? *)

(* We can't use
   Coercion Z_of_nat : nat >-> Z.
   Because
   Opaque Z_of_nat.
   makes all proofs with omega to fail
*)

Definition my_Z_of_nat := Z_of_nat.

Lemma my_Z_of_nat_def : my_Z_of_nat = Z_of_nat.
Proof using. reflexivity. Qed.

Global Opaque my_Z_of_nat.

Coercion my_Z_of_nat : nat >-> Z.


(* ********************************************************************** *)
(** * Conversion to natural numbers, for tactic programming *)

Definition ltac_nat_from_int (x:Z) : nat :=
  match x with
  | Z0 => 0%nat
  | Zpos p => nat_of_P p
  | Zneg p => 0%nat
  end.

Ltac nat_from_number N ::=
  match type of N with
  | nat => constr:(N)
  | int => let N' := constr:(ltac_nat_from_int N) in eval compute in N'
  | Z => let N' := constr:(ltac_nat_from_int N) in eval compute in N'
  (*todo: last case not needed*)
  end.


(* ********************************************************************** *)
(** * Inhabited *)

Instance int_inhab : Inhab int.
Proof using. intros. apply (prove_Inhab 0). Qed.


(* ********************************************************************** *)
(** * Comparable *)

(**************************************************************)
(** ** Extension to Stdlib comparisons *)

(* TODO: remove dependency on stdlib by removing following two lemmas *)

Definition comparison_compare c1 c2 :=
  match c1, c2 with
  | Eq, Eq => true
  | Datatypes.Lt, Datatypes.Lt => true
  | Datatypes.Gt, Datatypes.Gt => true
  | _, _ => false
  end.

Global Instance comparison_comparable : Comparable comparison.
  applys comparable_beq comparison_compare. intros x y.
  destruct x; destruct y; simpl; rew_refl; iff H; inverts~ H;
   tryfalse; auto; try congruence.
Qed.

Global Instance int_comparable : Comparable int.
Proof using.
  applys comparable_beq (fun i j => decide (i ?= j = Eq)). intros x y.
  simpl; rew_refl; iff H; rewrite Z.compare_eq_iff in * |- *; auto.
Qed.


(* ********************************************************************** *)
(** * Order on numbers *)

Instance le_int_inst : Le int := Build_Le Zle.


(* ---------------------------------------------------------------------- *)
(** ** Relation to Peano, for tactic [omega] *)

Lemma le_zarith : le = Zle.
Proof using. extens*. Qed.

Global Opaque le_int_inst.

Lemma lt_zarith : lt = Zlt.
Proof using.
  extens. rew_to_le. rewrite le_zarith.
  unfold strict. intros. omega.
Qed.

Lemma ge_zarith : ge = Zge.
Proof using.
  extens. rew_to_le. rewrite le_zarith.
  unfold flip. intros. omega.
Qed.

Lemma gt_zarith : gt = Zgt.
Proof using.
  extens. rew_to_le. rewrite le_zarith.
  unfold strict, flip. intros. omega.
Qed.

Hint Rewrite le_zarith lt_zarith ge_zarith gt_zarith : rew_int_comp.
Ltac int_comp_to_zarith :=
  autorewrite with rew_int_comp in *.



(* ********************************************************************** *)
(** * Decision procedure: calling [omega] *)

(** [is_arity_type T] returns a boolean indicating whether
    [T] is equal to [nat] or [int] *)

Ltac is_arith_type T :=
  match T with
  | nat => constr:(true)
  | int => constr:(true)
  | _ => constr:(false)
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
    | true => generalize H; clear H (* todo: revert H? *)
    | false => clear H
    end
  end.

(* TODO:
Ltac split_if_eq_bool :=
  let go _ := apply eq_bool_prove; intros in
  match goal with
  | |- @eq bool _ _ => go tt
  | |- istrue (@eqb bool _ _ _) => apply eq_to_equ; go tt
  end.
*)

(** Two lemmas to help omega out *)

Lemma Z_of_nat_O :
  Z_of_nat O = 0.
Proof using. reflexivity. Qed.

Lemma Z_of_nat_S : forall n,
  Z_of_nat (S n) = Zsucc (Z_of_nat n).
Proof using. intros. rewrite~ <- Zpos_P_of_succ_nat. Qed.

Lemma Z_of_nat_plus1 : forall n,
  Z_of_nat (1 + n) = Zsucc (Z_of_nat n).
Proof using. intros. rewrite <- Z_of_nat_S. fequals~. Qed.

(** [rew_maths] rewrite any lemma in the base [rew_maths].
    The goal should not contain any evar, otherwise tactic might loop. *)

Hint Rewrite my_Z_of_nat_def Z_of_nat_O Z_of_nat_S Z_of_nat_plus1 : rew_maths.

Ltac rew_maths :=
  autorewrite with rew_maths in *.

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

(* todo; [int_nat_conv]
Lemma int_nat_plus : forall (n m:nat),
  (n + m)%nat = (n + m)%Z :> int.
Proof using. applys inj_plus. Qed.
Hint Rewrite int_nat_plus : int_nat_conv.
*)

(** [math] tactics performs several preprocessing step,
    selects all arithmetic hypotheses, and the call omega. *)
(* todo: autorewrite with int_nat_conv in *. after int_comp_to_zarith *)

(* TODO *)
Ltac check_noevar_goal ::=
  match goal with |- ?G => first [ has_evar G; fail 1 | idtac ] end.

Ltac math_0 := idtac.
Ltac math_1 := intros; generalize_arith.
(* Work around for the slow [autorewrite in *] *)
Ltac math_2 := instantiate; check_noevar_goal.
Ltac math_3 := autorewrite with rew_maths rew_int_comp rew_nat_comp; intros.
(* original:
Ltac math_2 := instantiate; check_noevar_goal; intros.
Ltac math_3 := rew_maths; nat_comp_to_peano; int_comp_to_zarith.
*)
Ltac math_4 := math_setup_goal.
Ltac math_5 := omega.

Ltac math_debug := math_0; math_1; math_2; math_3; math_4.
Ltac math_base := math_debug; math_5.

Ltac math_lia := math_debug; lia.
Ltac math_nia := math_debug; nia.

Tactic Notation "math" := math_base.

Tactic Notation "math" simple_intropattern(I) ":" constr(E) :=
  asserts I: E; [ math | ].
Tactic Notation "maths" constr(E) :=
  let H := fresh "H" in asserts H: E; [ math | ].
(* todo: parsing conflit *)

(* ---------------------------------------------------------------------- *)
(** ** [math_lia], [math_nia], [math_dia] tactic *)

(* Require CSDP to be installed *)

(** [math_lia] supports linear arithmetic; it roughly provides the
    combined power of [ring_simplify] and [omega]. *)

Tactic Notation "math_lia" := math_debug; lia.

(** [math_nia] supports non-linear integer arithmetic.
    It performs a limited amount of non-linear reasoning
    before running [lia]. *)

Tactic Notation "math_nia" := math_debug; nia.

(** [math_dia] extends [math_nia] with support for divisions.
    Division are encoded using multiplications, via Euclidian
    division and remainder. *)

Definition Zdiv_hyp (P:Prop) := P.

Lemma Z_div_mod' : forall a b : int,
  Zdiv_hyp ((b > 0)%Z) ->
  let (q, r) := Z.div_eucl a b in
  a = (b * q)%I + r /\ (0 <= r < b)%Z.
Proof using. applys Z_div_mod. Qed.

Ltac Zdiv_eliminate_step tt :=
  match goal with |- context[ Z.div_eucl ?X ?Y ] =>
     generalize (@Z_div_mod' X Y);
     destruct (Z.div_eucl X Y)
  end.

Ltac math_dia_generalize_all_prop tt :=
  repeat match goal with H: ?T |- _ =>
    match type of T with Prop => gen H end end.

Ltac Zdiv_eliminate tt :=
  math_dia_generalize_all_prop tt;
  unfold Z.div;
  repeat (Zdiv_eliminate_step tt).

(* todo: deal differently with iterated divisions,
   in order to avoid blow up *)

Ltac Zdiv_instantiate_hyp_steps tt :=
  match goal with H: Zdiv_hyp ?P -> _ |- _ =>
    specializes H __;
    [ idtac
    | try Zdiv_instantiate_hyp_steps tt ]
  end.

Ltac Zdiv_instantiate_hyp tt :=
  Zdiv_instantiate_hyp_steps tt.

Ltac math_dia_setup :=
  math_0; math_1; math_2; math_3; Zdiv_eliminate tt;
  intros; try Zdiv_instantiate_hyp_steps tt; unfolds Zdiv_hyp.

Tactic Notation "math_dia" :=
  math_dia_setup; math_nia.

(*--in progress

Lemma math_nia_demo_1 : forall (a b N : int),
  N > 0 ->
  a * N <= b * N ->
  a <= b.
Proof using. math_nia. Qed.

Lemma math_dia_demo_1 : forall (a b t : int),
  t > 0 ->
  a <= b ->
  a / t <= b / t.
Proof using. math_dia. Qed.

Lemma math_dia_demo_2 : forall (a t : int),
  t > 1 ->
  a > 0 ->
  a / t <= a.
Proof using. math_dia. Qed.

Lemma math_dia_demo_3 : forall (a b t : int),
  t > 0 ->
  0 <= a <= b ->
  a / t <= b / t.
Proof using. math_dia. Qed.

Lemma math_dia_demo_4 : forall (a b N : int),
  N > 0 ->
  a > 0 ->
  b > 0 ->
  a * N <= b * N ->
  a <= b.
Proof using. math_dia. Qed.

Lemma math_dia_demo_5 : forall (a b N t : int),
  N > 0 ->
  t > 1 ->
  a > 0 ->
  b > 0 ->
  a * N <= b * N ->
  a / t <= b.
Proof using.
  intros.
  (* math_dia_setup. math_dia. *)
  try math_dia.
  assert (a / t <= a). math_dia.
  assert (a <= b). math_dia.
  math_dia.
Qed.

Lemma math_dia_demo_span_1 : forall (a b t n N : int),
  N > 0 ->
  n > 0 ->
  t > 0 ->
  a >= 0 ->
  b >= 0 ->
  a <= b * (1 + N/t) + n * t/N ->
  (   a <= b * (1 + N/t) + (n+1) * t/N
  /\ (a+1) <= (b+1) * (1 + N/t) + (n+1) * t/N
  /\ b * (1 + N/t) + N * t/N = b * (1 + t/N) + t
  /\ (b + t) * (1 + N/t) + n * t/N = b * (1 + N/t) + t + N + n * t/N).
Proof using.
  intros. splits.
  math_dia.
  try math_dia. skip.
  try math_dia. skip.
  try math_dia. skip.
Qed.

Lemma math_dia_demo : forall a b t n N,
  a * N <= b * N + (b + n) * t  ->
  a <= b * (1 + t / N) + n * t / N.
Proof using. intros. math_dia. Qed.
---*)


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
(** ** Calling [maths] after eliminating boolean reflection *)

(** [maths] is a more powerful version of [math],
    able to deconstruct conjunctions, disjunctions,
    and negations, but as a consequence it might be slower. *)

Hint Rewrite istrue_and istrue_or istrue_neg : rew_reflect_and_or_neg.

Ltac maths_core tt :=
  autorewrite with rew_reflect_and_or_neg in *; intuition math.

Tactic Notation "maths" :=
  maths_core tt.

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
(** ** Hint externs for calling math in the hint base [maths] *)

Ltac math_hint := math.

Hint Extern 3 (_ = _ :> nat) => math_hint : maths.
Hint Extern 3 (_ = _ :> int) => math_hint : maths.
Hint Extern 3 (_ <> _ :> nat) => math_hint : maths.
Hint Extern 3 (_ <> _ :> int) => math_hint : maths.
Hint Extern 3 (istrue (isTrue (_ = _ :> nat))) => math_hint : maths.
Hint Extern 3 (istrue (isTrue (_ = _ :> int))) => math_hint : maths.
Hint Extern 3 (istrue (isTrue (_ <> _ :> nat))) => math_hint : maths.
Hint Extern 3 (istrue (isTrue (_ <> _ :> int))) => math_hint : maths.
Hint Extern 3 ((_ <= _)%nat) => math_hint : maths.
Hint Extern 3 ((_ >= _)%nat) => math_hint : maths.
Hint Extern 3 ((_ < _)%nat) => math_hint : maths.
Hint Extern 3 ((_ > _)%nat) => math_hint : maths.
Hint Extern 3 ((_ <= _)%Z) => math_hint : maths.
Hint Extern 3 ((_ >= _)%Z) => math_hint : maths.
Hint Extern 3 ((_ < _)%Z) => math_hint : maths.
Hint Extern 3 ((_ > _)%Z) => math_hint : maths.
Hint Extern 3 (@le nat _ _ _) => math_hint : maths.
Hint Extern 3 (@lt nat _ _ _) => math_hint : maths.
Hint Extern 3 (@ge nat _ _ _) => math_hint : maths.
Hint Extern 3 (@gt nat _ _ _) => math_hint : maths.
Hint Extern 3 (@le int _ _ _) => math_hint : maths.
Hint Extern 3 (@lt int _ _ _) => math_hint : maths.
Hint Extern 3 (@ge int _ _ _) => math_hint : maths.
Hint Extern 3 (@gt int _ _ _) => math_hint : maths.
Hint Extern 3 (~ @le int _ _ _) => unfold not; math_hint : maths.
Hint Extern 3 (~ @lt int _ _ _) => unfold not; math_hint : maths.
Hint Extern 3 (~ @ge int _ _ _) => unfold not; math_hint : maths.
Hint Extern 3 (~ @gt int _ _ _) => unfold not; math_hint : maths.
Hint Extern 3 (~ @eq int _ _) => unfold not; math_hint : maths.
Hint Extern 3 (@le int _ _ _ -> False) => math_hint : maths.
Hint Extern 3 (@lt int _ _ _ -> False) => math_hint : maths.
Hint Extern 3 (@ge int _ _ _ -> False) => math_hint : maths.
Hint Extern 3 (@gt int _ _ _ -> False) => math_hint : maths.

(* ---------------------------------------------------------------------- *)
(** ** Extend [zify] to handle [Z.to_nat]. *)

Lemma Z_of_nat_zify : forall x, Z.of_nat (Z.to_nat x) = Z.max 0 x.
Proof.
  intros x. destruct x.
  - rewrite Z2Nat.id; reflexivity.
  - rewrite Z2Nat.inj_pos. math_lia.
  - rewrite Z2Nat.inj_neg. math_lia.
Qed.

Ltac zify_nat_op_extended :=
  match goal with
  | H : context [ Z.of_nat (Z.to_nat ?a) ] |- _ => rewrite (Z_of_nat_zify a) in H
  | |- context [ Z.of_nat (Z.to_nat ?a) ] => rewrite (Z_of_nat_zify a)
  | _ => zify_nat_op
  end.

Ltac zify_nat ::= repeat zify_nat_rel; repeat zify_nat_op_extended; unfold Z_of_nat' in *.

(* ********************************************************************** *)
(** * Simplification lemmas *)

(* ---------------------------------------------------------------------- *)
(** ** Addition and substraction *)

Lemma plus_zero_r : forall n,
  n + 0 = n.
Proof using. math. Qed.
Lemma plus_zero_l : forall n,
  0 + n = n.
Proof using. math. Qed.
Lemma minus_zero : forall n,
  n - 0 = n.
Proof using. math. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Comparison *)

Lemma plus_le_l : forall a b c,
  (a + b <= a + c) = (b <= c).
Proof using. math. Qed.
Lemma plus_ge_l : forall a b c,
  (a + b >= a + c) = (b >= c).
Proof using. math. Qed.
Lemma plus_lt_l : forall a b c,
  (a + b < a + c) = (b < c).
Proof using. math. Qed.
Lemma plus_gt_l : forall a b c,
  (a + b > a + c) = (b > c).
Proof using. math. Qed.

Lemma plus_le_r : forall a b c,
  (b + a <= c + a) = (b <= c).
Proof using. math. Qed.
Lemma plus_ge_r : forall a b c,
  (b + a >= c + a) = (b >= c).
Proof using. math. Qed.
Lemma plus_lt_r : forall a b c,
  (b + a < c + a) = (b < c).
Proof using. math. Qed.
Lemma plus_gt_r : forall a b c,
  (b + a > c + a) = (b > c).
Proof using. math. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Simplification tactic *)

(** [rew_int] performs some basic simplification on
    expressions involving integers *)

Hint Rewrite plus_zero_r plus_zero_l minus_zero : rew_int.
Hint Rewrite plus_le_l plus_ge_l plus_lt_l plus_gt_l : rew_int.
Hint Rewrite plus_le_r plus_ge_r plus_lt_r plus_gt_r : rew_int.

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


(************************************************************)
(* * Relation with Nat *)

(** Proofs below using stdlib *)

Notation "'abs'" := Zabs_nat (at level 0).

Global Opaque Zabs Zabs_nat.

Lemma abs_pos_nat : forall n : nat,
  abs n = n.
Proof using. exact Zabs_nat_Z_of_nat. Qed.

Lemma abs_pos : forall n : int,
  n >= 0 -> abs n = n :> int.
Proof using.
  intros. rewrite inj_Zabs_nat.
  rewrite Zabs_eq. math. math.
Qed.

(* TODO: make names below more uniform *)

Lemma eq_int_nat : forall n m : nat,
  n = m :> int -> n = m :> nat.
Proof using. math. Qed.

Lemma nat_int_lt : forall (x y:nat),
  (x:int) < (y:int) -> (x < y)%nat.
Proof using. math. Qed.

Lemma nat_int_neq : forall (x y:nat),
  (x:int) <> (y:int) -> (x <> y)%nat.
Proof using. math. Qed.

Lemma nat_int_le : forall (x y:nat),
  x <= y -> ((x:int) <= (y:int)).
Proof. math. Qed.

Lemma nat_int_ge : forall (x y:nat),
  x >= y -> ((x:int) >= (y:int)).
Proof. math. Qed.

Lemma succ_abs : forall n : int,
  n >= 0 -> S (abs n) = abs (1 + n) :> nat.
Proof using.
  intros n. pattern n. applys (@measure_induction _ abs). clear n.
  intros n IH Pos. rewrite <- Zabs_nat_Zsucc. fequals. math. math.
Qed.

Lemma abs_spos : forall n : int,
  n > 0 -> abs n = S (abs (n-1)) :> nat.
Proof using.
  intros. apply eq_int_nat.
  rewrite abs_pos; try math.
  rewrite succ_abs; try math.
  rewrite abs_pos; math.
Qed.

Lemma int_nat_eq : forall (x y:nat),
  (x = y :> int) -> (x = y :> nat).
Proof using. math. Qed.

Lemma int_nat_le : forall (x y:nat),
  ((x:int) <= (y:int)) -> x <= y.
Proof using. math. Qed.

Lemma int_nat_lt : forall (x y:nat),
  x < y -> (x:int) < (y:int).
Proof using. math. Qed.

Lemma Zabs_nat_lt : forall n m,
  (0 <= n) -> (n < m) -> (abs n < abs m).
Proof using.
  intros. nat_comp_to_peano. apply Zabs_nat_lt. math.
Qed.

Lemma abs_plus : forall a b : int,
  (a >= 0) -> (b >= 0) ->
  abs (a+b) = (abs a + abs b)%nat :> nat.
Proof using. intros. applys Zabs2Nat.inj_add; math. Qed.

Lemma abs_minus : forall a b : int,
  (a >= b) -> (b >= 0) ->
  abs (a-b) = (abs a - abs b)%nat :> nat.
Proof using. intros. applys Zabs2Nat.inj_sub; math. Qed.

Lemma plus_nat_int : forall a b : nat,
  (a+b)%nat = (a:int) + (b:int) :> int.
Proof using.
  Transparent my_Z_of_nat.
  intros. unfold my_Z_of_nat. applys Nat2Z.inj_add.
Qed.

Hint Rewrite plus_nat_int : rew_maths.

Lemma abs_1 : abs 1 = 1%nat :> nat.
Proof using. reflexivity. Qed.

Hint Rewrite abs_plus abs_1 abs_pos abs_pos_nat : rew_abs_pos.
Tactic Notation "rew_abs_pos" :=
  autorewrite with rew_abs_pos.
Tactic Notation "rew_abs_pos" "~" :=
  autorewrite with rew_abs_pos; try math; autos~.

Lemma mod_eq_prove : forall k a b n,
  a = b + k * n -> a mod n = b mod n.
Proof using. intros. subst. rewrite~ Z_mod_plus_full. Qed.

Lemma mod_prove : forall k a b n,
  a = b + k * n -> 0 <= b -> b < n -> a mod n = b.
Proof using.
  intros. rewrite <- (@Zmod_small b n).
  apply* mod_eq_prove. math.
Qed.

Lemma mod2_zero :
  0 mod 2 = 0.
Proof using. reflexivity. Qed.
Lemma mod2_odd : forall k,
  (2 * k) mod 2 = 0.
Proof using. intros. apply (mod_prove k); math. Qed.
Lemma mod2_even : forall k,
  (2 * k + 1) mod 2 = 1.
Proof using. intros. apply (mod_prove k); math. Qed.
Lemma div2_odd : forall k,
  (2 * k) / 2 = k.
Proof using.
  intros. math_rewrite (2*k=k*2).
  apply Z_div_mult_full. math.
Qed.
Lemma div2_even : forall k,
  k >= 0 -> (2 * k + 1) / 2 = k.
Proof using. intros. symmetry. eapply Zdiv_unique with (r:=1); math. Qed.

Lemma mod2_bound : forall n,
  0 <= n mod 2 < 2.
Proof using. (* using stdlib *)
  intros. forwards: (Z_mod_remainder n 2). math.
  destruct H as [[? ?]|[? ?]]; math.
Qed.

Lemma div2_bounds : forall m n,
  m = n / 2 -> 2 * m <= n /\ n <= 2 * m + 1.
Proof using. (* using stdlib *)
  intros. lets K: (Z_div_mod_eq n 2) __. math. (* TODO: forwards shouldn't do simpl *)
  rewrite <- H in K.
  lets [E1 E2]: (mod2_bound n). math.
Qed.

Implicit Arguments div2_bounds [m n].

Hint Rewrite mod2_zero mod2_odd mod2_even div2_odd div2_even : rew_parity.

Ltac rew_parity :=
  autorewrite with rew_parity.


(************************************************************)
(* * Elimination of multiplication, to call omega *)

Lemma double : forall x, 2 * x = x + x.
Proof using. intros. ring. Qed.

Lemma triple : forall x, 3 * x = x + x + x.
Proof using. intros. ring. Qed.

Lemma quadruple : forall x, 3 * x = x + x + x.
Proof using. intros. ring. Qed.

(* To use [math] with simple multiplications, add the command:
   Hint Rewrite double triple : rew_maths.
*)


(************************************************************)
(* * Min function *)

Require Import LibEpsilon.

Instance int_le_total_order : Le_total_order (A:=int).
Proof using.
  constructor. constructor. constructor; unfolds.
  math. math. unfolds. math. unfolds.
  intros. tests: (x <= y). left~. right. math.
Qed.

(* todo: make polymorphic with classes *)

Section Min.
Implicit Types x y : int.

Definition min x y :=
  If x <= y then x else y.

Lemma min_self : forall x,
  min x x = x.
Proof using. intros. unfolds min. case_if~. Qed.
Lemma min_left : forall x y,
  x <= y -> min x y = x.
Proof using. intros. unfolds min. case_if~. false*. Qed.
Lemma min_right : forall x y,
  y <= x -> min x y = y.
Proof using. intros. unfolds min. case_if~. apply~ le_antisym. Qed.
Lemma min_trans_elim : forall a b x y : int,
  min a b <= x -> y < a -> y < b -> y < x.
Proof using. intros. unfolds min. case_if; math. Qed.

End Min.

(************************************************************)
(* * Pow function *)

Require Import Zpow_facts.

Lemma power_pos:
  forall k n,
  0 < n ->
  0 <= k ->
  1 <= n^k.
Proof using.
  intros. math_rewrite (1 = n^0). reflexivity.
  apply Zpower_le_monotone; math.
Qed.

Lemma pow2_pos : forall n, n >= 0 -> 2^n >= 1.
Proof using.
  intros. forwards: power_pos n 2; math.
Qed.

Lemma pow2_succ : forall n, n >= 0 -> 2^(n+1) = 2*2^n.
Proof using.
  intros. math_rewrite (n+1 = Zsucc n).
  rewrite Zpower_Zsucc; math.
Qed.

(* A tactic that helps dealing with goals containing "b^m" for multiple m *)
Require Import List.

Ltac subst_eq_boxer_list l rewrite_tac :=
  match l with
  | nil => idtac
  | (@boxer _ ?p) :: ?Hs =>
    match p with
      (?tm, ?Htm) =>
      rewrite_tac Htm; clear Htm; clear tm;
      subst_eq_boxer_list Hs rewrite_tac
    end
  end.

(* Develop occurences of (b ^ m) in H into (b ^ (m - min_e) * b ^ min_e).
   (and try to simplify/compute b^(m - min_e)).
 *)
Ltac rew_pow_develop b m min_e H :=
  let m_eq_plusminus := fresh in
  assert (m = min_e + (m - min_e)) as m_eq_plusminus
      by (rewrite Zplus_minus; reflexivity);
  rewrite m_eq_plusminus in H; clear m_eq_plusminus;
  rewrite (Z.pow_add_r b min_e (m - min_e)) in H; [
    rewrite Z.mul_comm in H;
    let tm' := fresh "tm'" in
    let H' := fresh "H'" in
    remember (b ^ (m - min_e)) as tm' eqn:H' in H;
    let e := fresh "e" in
    evar (e: int);
    let Heqe := fresh in
    assert (e = m - min_e) as Heqe
        by (ring_simplify; subst e; reflexivity);
    rewrite <-Heqe in H'; clear Heqe; unfold e in H'; ring_simplify in H';
    rewrite H' in H; clear H'; clear tm'; clear e;
    try rewrite Z.mul_1_l in H
  | ring_simplify; auto with zarith ..].

Ltac rew_pow_aux_goal b min_e normalized_acc :=
  match goal with
  | |- context [ b ^ ?m ] =>
    let tm := fresh "tm" in
    let Heqtm := fresh "Heqtm" in
    remember (b ^ m) as tm eqn:Heqtm in |- *;
    rew_pow_develop b m min_e Heqtm; [
      rew_pow_aux_goal b min_e ((boxer (tm, Heqtm)) :: normalized_acc)
    | ..]
  | _ => subst_eq_boxer_list normalized_acc ltac:(fun E => rewrite E)
  end.

Ltac rew_pow_aux_in b min_e H normalized_acc :=
  match type of H with
  | context [ b ^ ?m ] =>
    let tm := fresh "tm" in
    let Heqtm := fresh "Heqtm" in
    remember (b ^ m) as tm eqn:Heqtm in H;
    rew_pow_develop b m min_e Heqtm; [
      rew_pow_aux_in b min_e H ((boxer (tm, Heqtm)) :: normalized_acc)
    | ..]
  | _ => subst_eq_boxer_list normalized_acc ltac:(fun E => rewrite E in H)
  end.

Tactic Notation "rew_pow" constr(b) constr(min_e) :=
  rew_pow_aux_goal b min_e (@nil Boxer).
Tactic Notation "rew_pow" "~" constr(b) constr(min_e) :=
  rew_pow_aux_goal b min_e (@nil Boxer); auto_tilde.
Tactic Notation "rew_pow" "*" constr(b) constr(min_e) :=
  rew_pow_aux_goal b min_e (@nil Boxer); auto_star.
Tactic Notation "rew_pow" constr(b) constr(min_e) "in" hyp(H) :=
  rew_pow_aux_in b min_e H (@nil Boxer).
Tactic Notation "rew_pow" "~" constr(b) constr(min_e) "in" hyp(H) :=
  rew_pow_aux_in b min_e H (@nil Boxer); auto_tilde.
Tactic Notation "rew_pow" "*" constr(b) constr(min_e) "in" hyp(H) :=
  rew_pow_aux_in b min_e H (@nil Boxer); auto_star.

(* Test  -- TODO: move *)
(* Axiom P : int -> Prop.  *)
(* Goal forall n, P (1 + 2 ^ (n + 3) + 2 ^ n + 2 ^ (n+1)). *)
(* Proof. *)
(*   intros. *)
(*   skip_asserts: (3 = 2 ^ (n+3)). rew_pow 2 n in H. *)
(*   rew_pow 2 n. *)
(* Admitted. *)

(* ********************************************************************** *)
(** * Advanced induction *)

Definition eq_gt_implies (P : (nat->Prop) -> Prop) :=
  forall n, (forall m, n > m -> P (eq m)) -> P (gt n).

Definition eq_lt_implies (P : (nat->Prop) -> Prop) :=
  forall n, (forall m, n < m -> P (eq m)) -> P (gt n).

Hint Unfold eq_lt_implies eq_gt_implies.

Lemma eq_lt_induction : forall (P : (nat->Prop) -> Prop),
  (forall n, (forall m, n > m -> P (eq m)) -> P (lt n)) ->
  (forall n, P (lt n) -> P (eq n)) ->
  (forall n, P (eq n)).
Proof using. intros. induction n using peano_induction. auto. Qed.

Lemma eq_gt_induction : forall (P : (nat->Prop) -> Prop),
  (forall n, (forall m, n > m -> P (eq m)) -> P (gt n)) ->
  (forall n, P (gt n) -> P (eq n)) ->
  (forall n, P (eq n)).
Proof using. intros. induction n using peano_induction. auto. Qed.

Lemma eq_gt_induction_2 : forall (P1 P2 : (nat->Prop) -> Prop),
  eq_gt_implies P1 -> eq_gt_implies P2 ->
  (forall n, P1 (gt n) -> P2 (gt n) -> P1 (eq n) /\ P2 (eq n)) ->
  (forall n, P1 (eq n)) /\ (forall n, P2 (eq n)).
Proof using.
  introv H1 H2 R.
  cuts M: (forall n, P1 (eq n) /\ P2 (eq n)).
    split; intros n; specializes M n; autos*.
  induction n using peano_induction. apply R;
    match goal with K: eq_gt_implies ?Pi |- ?Pi _ =>
      apply K; intros; forwards*: H; try math end.
Qed.

(* todo: other arities *)

Lemma eq_gt_induction_5 : forall (P1 P2 P3 P4 P5 : (nat->Prop) -> Prop),
  eq_gt_implies P1 -> eq_gt_implies P2 -> eq_gt_implies P3 ->
  eq_gt_implies P4 -> eq_gt_implies P5 ->
  (forall n, P1 (gt n) -> P2 (gt n) -> P3 (gt n) -> P4 (gt n) -> P5 (gt n) ->
    P1 (eq n) /\ P2 (eq n) /\ P3 (eq n) /\ P4 (eq n) /\ P5 (eq n)) ->
  (forall n, P1 (eq n)) /\ (forall n, P2 (eq n)) /\ (forall n, P3 (eq n))
    /\ (forall n, P4 (eq n))  /\ (forall n, P5 (eq n)).
Proof using.
  introv H1 H2 H3 H4 H5 R.
  cuts M: (forall n, P1 (eq n) /\ P2 (eq n) /\ P3 (eq n) /\ P4 (eq n) /\ P5 (eq n)).
    splits; intros n; specializes M n; autos*.
  induction n using peano_induction. apply R;
    match goal with K: eq_gt_implies ?Pi |- ?Pi _ =>
      apply K; intros; forwards*: H; try math end.
Qed.

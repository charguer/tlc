(**************************************************************************
* TLC: A library for Coq                                                  *
* Tactics for integers arithmetic                                         *
**************************************************************************)

(** --IMPORTANT: requires the CSDP package to be installed on the system
    [sudo apt get install ubuntu package coinor-csdp]
*)

(** For documentation, see the Micrlia chapter from Coq reference manual:
    "Micrlia: tactics for solving arithmetic goals over ordered rings" *)


(** --DISCLAIMER: WORK IN PROGRESS *)


Set Implicit Arguments.
Require Import Coq.micromega.Psatz.
From TLC Require Import LibTactics.
From TLC Require Export LibInt.


(* ********************************************************************** *)
(** * Tactics *)

(* ---------------------------------------------------------------------- *)
(** ** [math_nia] tactic *)

(** [math_nia] supports non-linear integer arithmetic.
    It performs a limited amount of non-linear reasoning
    before running [lia]. *)

Ltac math_nia_core tt :=
  math_setup; nia.

Tactic Notation "math_nia" :=
  math_nia_core tt.

(** Binding for [nat] --TODO: is it useful? *)

Ltac nat_math_nia :=
  nat_math_setup; nia.


(* ---------------------------------------------------------------------- *)
(** ** [math_dia] *)

(** [math_dia] extends [math_nia] with support for divisions.
    Division are encoded using multiplications, via Euclidian
    division and remainder. *)

Definition Zdiv_hyp (P:Prop) := P.

Lemma Z_div_mod' : forall a b : Z,
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

(* --TODO: deal differently with iterated divisions,
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

Ltac math_dia_core tt :=
  math_dia_setup; math_nia.

Tactic Notation "math_dia" :=
  math_dia_core tt.



(* ********************************************************************** *)
(** * Demos *)

(** --Commented out so that the compilation does not fail in the absence
      of the CSDP package...

Lemma math_nia_demo_1 : forall (a b N : Z),
  N > 0 ->
  a * N <= b * N ->
  a <= b.
Proof using. math_nia. Qed.

Lemma math_dia_demo_1 : forall (a b t : Z),
  t > 0 ->
  a <= b ->
  a / t <= b / t.
Proof using. math_dia. Qed.

Lemma math_dia_demo_2 : forall (a t : Z),
  t > 1 ->
  a > 0 ->
  a / t <= a.
Proof using. math_dia. Qed.

Lemma math_dia_demo_3 : forall (a b t : Z),
  t > 0 ->
  0 <= a <= b ->
  a / t <= b / t.
Proof using. math_dia. Qed.

Lemma math_dia_demo_4 : forall (a b N : Z),
  N > 0 ->
  a > 0 ->
  b > 0 ->
  a * N <= b * N ->
  a <= b.
Proof using. math_dia. Qed.

Lemma math_dia_demo_5 : forall (a b N t : Z),
  N > 0 ->
  t > 1 ->
  a > 0 ->
  b > 0 ->
  a * N <= b * N ->
  a / t <= b.
Proof using. (* showing that a little help might be needed *)
  intros.
  (* math_dia_setup. math_dia. skip. *)
  try math_dia.
  assert (a / t <= a). math_dia.
  assert (a <= b). math_dia.
  math_dia.
Qed.

*)


(*--- FUTURE WORK
Lemma math_dia_demo_span_1 : forall (a b t n N : Z),
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

--*)


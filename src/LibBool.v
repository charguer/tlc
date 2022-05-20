(**************************************************************************
* TLC: A library for Coq                                                  *
* Reflection : Basic Operations on Booleans                               *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibOperation.


(* ********************************************************************** *)
(** * Boolean type *)

(* ---------------------------------------------------------------------- *)
(** ** Definition *)

(** From the Prelude:

  Inductive bool : Type :=
    | true : bool
    | false : bool.

*)

(* ---------------------------------------------------------------------- *)
(** ** Inhabited *)

#[global]
Instance Inhab_bool : Inhab bool.
Proof using. constructor. apply (Inhab_of_val true). Qed.


(* ---------------------------------------------------------------------- *)
(** ** Extensionality *)

(** See [LibReflect] for extensionality of booleans. *)


(* ********************************************************************** *)
(** * Boolean Operations *)

(** ** Comparison *)

Definition eqb (x y:bool) : bool :=
  match x, y with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

(** Negation *)

Definition neg (x:bool) : bool :=
  match x with
  | true => false
  | false => true
  end.

(** Conjunction *)

Definition and (x y:bool) : bool :=
  match x, y with
  | true, true => true
  | _, _ => false
  end.

(** Disjunction *)

Definition or (x y:bool) : bool :=
  match x, y with
  | false, false => false
  | _, _ => true
  end.

(** Implication *)

Definition impl (x y:bool) : bool :=
  or x (neg y).

(** Exclusive or *)

Definition xor (x y:bool) : bool :=
  neg (eqb x y).


(** Notations *)

Declare Scope Bool_scope.
Bind Scope Bool_scope with bool.
Open Scope Bool_scope.

Notation "! x" := (neg x)
  (at level 35, right associativity) : Bool_scope.
Infix "&&" := and
  (at level 40, left associativity) : Bool_scope.
Infix "||" := or
  (at level 50, left associativity) : Bool_scope.

Notation "! x" := (neg x)
  (at level 35, right associativity) : Bool_scope.
Infix "&&" := and
  (at level 40, left associativity) : Bool_scope.
Infix "||" := or
  (at level 50, left associativity) : Bool_scope.


(* ********************************************************************** *)
(** * Boolean Decision Procedure : tactic working by exponential case
      analysis on all variables of type bool. *)

(* ---------------------------------------------------------------------- *)
(** ** Tactic [tautob] *)

(** [tautob] introduces all variables that it can, performs a
    case analysis on all the boolean variables, then splits
    all subgoals and attempts resolution using intuition *)

Ltac tautob_post tt :=
  simpls; try split; intros; try discriminate;
  try solve [ intuition auto_false ].

Ltac tautob_core tt :=
  let rec aux tt :=
    (try intros_all); match goal with
    | b : bool |- _ => destruct b; clear b; aux tt
    | _ => tautob_post tt
    end in
  aux tt.

Tactic Notation "tautob" :=
  tautob_core tt.


(* ********************************************************************** *)
(** * Properties of boolean operators *)

(* ---------------------------------------------------------------------- *)
(** ** Properties of [eqb] *)

Lemma eqb_same : forall x,
  eqb x x = true.
Proof using. tautob. Qed.

Lemma eqb_true_l : neutral_l eqb true.
(* forall x, eqb true x = x. *)
Proof using. tautob. Qed.

Lemma eqb_true_r : neutral_r eqb true.
Proof using. tautob. Qed.

Lemma eqb_false_l : forall x,
  eqb false x = neg x.
Proof using. tautob. Qed.

Lemma eqb_false_r : forall x,
  eqb x false = neg x.
Proof using. tautob. Qed.

Lemma eqb_comm : comm eqb.
Proof using. tautob. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Properties of [and] *)

Lemma and_same : idempotent2 and.
Proof using. tautob. Qed.

Lemma and_true_l : neutral_l and true.
Proof using. tautob. Qed.

Lemma and_true_r : neutral_r and true.
Proof using. tautob. Qed.

Lemma and_false_l : absorb_l and false.
Proof using. tautob. Qed.

Lemma and_false_r : absorb_r and false.
Proof using. tautob. Qed.

Lemma and_comm : comm and.
Proof using. tautob. Qed.

Lemma and_assoc : assoc and.
Proof using. tautob. Qed.

Lemma and_or_l : distrib_r and or.
(* forall x y z, (x || y) && z = x && z ||| y && z. *)
Proof using. tautob. Qed.

Lemma and_or_r : distrib_l and or.
(* forall x y z, x && (y ||| z) = x && y ||| x && z. *)
Proof using. tautob. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Properties of [or] *)

Lemma or_same : idempotent2 or.
Proof using. tautob. Qed.

Lemma or_false_l : neutral_l or false.
Proof using. tautob. Qed.

Lemma or_false_r : neutral_r or false.
Proof using. tautob. Qed.

Lemma or_true_l : absorb_l or true.
Proof using. tautob. Qed.

Lemma or_true_r : absorb_r or true.
Proof using. tautob. Qed.

Lemma or_comm : comm or.
Proof using. tautob. Qed.

Lemma or_assoc : assoc or.
Proof using. tautob. Qed.

Lemma or_and_l : distrib_r or and.
(* forall x y z, (x && y) || z = (x || z) && (y || z). *)
Proof using. tautob. Qed.

Lemma or_and_r : distrib_l or and.
(* forall x y z, x || (y && z) = (x || y) && (x || z). *)
Proof using. tautob. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Properties of [neg] *)

Lemma neg_false : ! false = true.
Proof using. auto. Qed.

Lemma neg_true : ! true = false.
Proof using. auto. Qed.

(* --LATER: fix coq display of goals below *)

Lemma neg_and : automorphism neg and or.
(* forall x y, ! (x && y) = (! x) || (! y) *)
Proof using. tautob. Qed.

Lemma neg_or : automorphism neg or and.
(* forall x y, ! (x || y) = (! x) && (! y) *)
Proof using. tautob. Qed.

Lemma neg_neg : involutive neg.
(* forall x, ! (! b) = b *)
Proof using. tautob. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Properties of [if then else] *)

Section PropertiesIf.
Implicit Types x y z : bool.

Lemma if_true : forall x y,
  (if true then x else y) = x.
Proof using. auto. Qed.

Lemma if_false : forall x y,
  (if false then x else y) = y.
Proof using. auto. Qed.

Lemma if_then_else_same : forall x y,
  (if x then y else y) = y.
Proof using. tautob. Qed.

Lemma if_then_true_else_false : forall x,
  (if x then true else false) = x.
Proof using. tautob. Qed.

Lemma if_then_false_else_true : forall x,
  (if x then false else true) = !x.
Proof using. tautob. Qed.

Lemma if_then_true : forall x y,
  (if x then true else y) = x || y.
Proof using. tautob. Qed.

Lemma if_then_false : forall x y,
  (if x then false else y) = (!x) && y.
Proof using. tautob. Qed.

Lemma if_else_false : forall x y,
  (if x then y else false) = x && y.
Proof using. tautob. Qed.

Lemma if_else_true : forall x y,
  (if x then y else true) = (!x) || y.
Proof using. tautob. Qed.

End PropertiesIf.


(* ---------------------------------------------------------------------- *)
(** ** Properties of [impl] and [xor] *)

(** We do not provide lemmas for [impl] and [xor]
   because these functions can be easily expressed
   in terms of the other operators. *)


(* ---------------------------------------------------------------------- *)
(** ** Opacity *)

Opaque eqb neg and or.


(* ********************************************************************** *)
(** * Tactics *)

(* ---------------------------------------------------------------------- *)
(** ** Tactic [rew_neg_neg] *)

(** [rew_neg_neg] is a tactic that simplifies all double negations
    of booleans, i.e. replaces [!!b] with [b]. *)

#[global]
Hint Rewrite neg_neg : rew_neg_neg.

Tactic Notation "rew_neg_neg" :=
  autorewrite with rew_neg_neg.
Tactic Notation "rew_neg_neg" "~" :=
  rew_neg_neg; auto_tilde.
Tactic Notation "rew_neg_neg" "*" :=
  rew_neg_neg; auto_star.
Tactic Notation "rew_neg_neg" "in" hyp(H) :=
  autorewrite with rew_neg_neg in H.
Tactic Notation "rew_neg_neg" "~" "in" hyp(H) :=
  rew_neg_neg in H; auto_tilde.
Tactic Notation "rew_neg_neg" "*" "in" hyp(H) :=
  rew_neg_neg in H; auto_star.
Tactic Notation "rew_neg_neg" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_neg_neg).
  (* autorewrite with rew_neg_neg in *. *)
Tactic Notation "rew_neg_neg" "~" "in" "*" :=
  rew_neg_neg in *; auto_tilde.
Tactic Notation "rew_neg_neg" "*" "in" "*" :=
  rew_neg_neg in *; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [rew_bool] *)

(** [rew_bool] simplifies boolean expressions, using rewriting
    lemmas in the database [rew_bool] defined below. *)

#[global]
Hint Rewrite
  eqb_same eqb_true_l eqb_true_r eqb_false_l eqb_false_r
  neg_false neg_true neg_neg neg_and neg_or
  and_true_l and_true_r and_false_l and_false_r
  or_false_l or_false_r or_true_l or_true_r
  if_true if_false if_then_else_same
  if_then_true_else_false if_then_false_else_true
  if_then_true if_else_false
  if_then_false if_else_true
  : rew_bool.

Tactic Notation "rew_bool" :=
  autorewrite with rew_bool.
Tactic Notation "rew_bool" "~" :=
  rew_bool; auto_tilde.
Tactic Notation "rew_bool" "*" :=
  rew_bool; auto_star.
Tactic Notation "rew_bool" "in" hyp(H) :=
  autorewrite with rew_bool in H.
Tactic Notation "rew_bool" "~" "in" hyp(H) :=
  rew_bool in H; auto_tilde.
Tactic Notation "rew_bool" "*" "in" hyp(H) :=
  rew_bool in H; auto_star.
Tactic Notation "rew_bool" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_bool).
  (* autorewrite with rew_bool in *. *)
Tactic Notation "rew_bool" "~" "in" "*" :=
  rew_bool in *; auto_tilde.
Tactic Notation "rew_bool" "*" "in" "*" :=
  rew_bool in *; auto_star.


(**************************************************************************
* TLC: A library for Coq                                                  *
* Reflection : Basic Operations on Booleans                               *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibOperation.

(* ********************************************************************** *)
(** * Properties of the boolean type *)

(* ---------------------------------------------------------------------- *)
(** ** Inhabited *)

Instance bool_inhab : Inhab bool.
Proof using. constructor. apply (prove_Inhab true). Qed.

(** For [Extensional bool], see file LibReflect:
    this result is not in [LibBool] because it depends on definition
    from [LibReflect], which itself depends on [LibBool]. *)


(* ********************************************************************** *)
(** * Boolean Operations *)

(* TODO: is it possible to reuse the definition from the library?
   It might be possible, but it requires to fix several proofs *)

Section Definitions.
Implicit Types x y z : bool.

(** ** Comparison *)

Definition eqb x y :=
  match x, y with
  | true, true => true
  | false, false => true
  | _, _ => false
  end.

(** Conjunction *)

Definition and x y :=
  match x, y with
  | true, true => true
  | _, _ => false
  end.

(** Disjunction *)

Definition or x y :=
  match x, y with
  | false, false => false
  | _, _ => true
  end.

(** Implication *)

Definition impl x y :=
  match x, y with
  | false, true => false
  | _, _ => true
  end.

(** Negation *)

Definition neg x :=
  match x with
  | true => false
  | false => true
  end.

(** Exclusive or*)

Definition xor x y :=
  x <> y.

End Definitions.

(** Notations *)

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

Infix "&&&" := and
  (at level 40, left associativity, only parsing) : Bool_scope.
Infix "|||" := or
  (at level 50, left associativity, only parsing) : Bool_scope.
  (* todo: understand why there is a bug on the && *)

Bind Scope Bool_scope with bool.
Open Scope Bool_scope.



(* ********************************************************************** *)
(** * Boolean Decision Procedure : tactic working by exponential case
      analysis on all variables of type bool. *)

(* ---------------------------------------------------------------------- *)
(** ** A first simple tactic named [tautob]. *)

Tactic Notation "tautob" :=
  let rec go _ :=
    (try intros_all); match goal with
    | b : bool |- _ => destruct b; clear b; go tt
    | _ => simpls; try split; intros; try discriminate
    end in go tt.

Tactic Notation "tautob" "~" :=
   tautob; auto_tilde.
Tactic Notation "tautob" "*" :=
   tautob; auto_star.


(* ********************************************************************** *)
(** * Properties of booleans *)

(* ---------------------------------------------------------------------- *)
(** ** Properties of [and], [or] and [neg] *)

(* todo: rename those lemmas according to convention (e.g. and_neutral_l) *)

Lemma or_same : idempotent2 or.
Proof using. tautob~. Qed.

Lemma and_same : idempotent2 and.
Proof using. tautob~. Qed.

Lemma and_true_l : neutral_l and true.
Proof using. tautob~. Qed.

Lemma and_true_r : neutral_r and true.
Proof using. tautob~. Qed.

Lemma and_false_l : absorb_l and false.
Proof using. tautob~. Qed.

Lemma and_false_r : absorb_r and false.
Proof using. tautob~. Qed.

Lemma or_false_l : neutral_l or false.
Proof using. tautob~. Qed.

Lemma or_false_r : neutral_r or false.
Proof using. tautob~. Qed.

Lemma or_true_l : absorb_l or true.
Proof using. tautob~. Qed.

Lemma or_true_r : absorb_r or true.
Proof using. tautob~. Qed.

Lemma comm_or : comm or.
Proof using. tautob~. Qed.

Lemma comm_and : comm and.
Proof using. tautob~. Qed.

Lemma assoc_and : assoc and.
Proof using. tautob*. Qed.

Lemma assoc_or : assoc or.
Proof using. tautob*. Qed.

Lemma neg_false : ! false = true.
Proof using. auto. Qed.

Lemma neg_true : ! true = false.
Proof using. auto. Qed.

Lemma neg_and : @automorphism bool neg and or.
Proof using. tautob~. Qed.

Lemma neg_or : @automorphism bool neg or and.
Proof using. tautob~. Qed.

Lemma neg_neg : involutive neg.
Proof using. tautob~. Qed.

Lemma distribute_and : forall x y z,
  (x ||| y) &&& z = x &&& z ||| y &&& z.
Proof. tautob~. Qed.

Lemma distribute_or : forall x y z,
  x &&& y ||| z = (x ||| z) &&& (y ||| z).
Proof. tautob~. Qed.


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
Proof using. tautob~. Qed.

Lemma if_then_true_else_false : forall x,
  (if x then true else false) = x.
Proof using. tautob~. Qed.

Lemma if_then_false_else_true : forall x,
  (if x then false else true) = !x.
Proof using. tautob~. Qed.

Lemma if_then_true : forall x y,
  (if x then true else y) = x || y.
Proof using. tautob~. Qed.

Lemma if_then_false : forall x y,
  (if x then false else y) = (!x) && y.
Proof using. tautob~. Qed.

Lemma if_else_false : forall x y,
  (if x then y else false) = x && y.
Proof using. tautob~. Qed.

Lemma if_else_true : forall x y,
  (if x then y else true) = (!x) || y.
Proof using. tautob~. Qed.

End PropertiesIf.


(* ********************************************************************** *)
(** * Tactics *)

(** [fix_neg_neg] is a tactic that simplifies all double negations. *)

Hint Rewrite neg_neg : rew_neg_neg.
Tactic Notation "fix_neg_neg" :=
  autorewrite with rew_neg_neg in *.
Tactic Notation "fix_neg_neg" "~" :=
  fix_neg_neg; auto_tilde.
Tactic Notation "fix_neg_neg" "*" :=
  fix_neg_neg; auto_star.

(** [rew_bool] simplifies boolean expressions, using rewriting
    lemmas in the database [rew_bool] defined below. *)

Hint Rewrite
  neg_false neg_true neg_neg neg_and neg_or
  and_true_l and_true_r and_false_l and_false_r
  or_false_l or_false_r or_true_l or_true_r
  if_true if_false if_then_else_same 
  if_then_true_else_false if_then_false_else_true 
  if_then_true if_else_false
  if_then_false if_else_true
  : bool_rew.

Tactic Notation "rew_bool" :=
  autorewrite with bool_rew.
Tactic Notation "rew_bool" "in" hyp(H) :=
  autorewrite with bool_rew in H.
Tactic Notation "rew_bool" "in" "*":=
  autorewrite with bool_rew in *.
Tactic Notation "rew_bool" "~" :=
  rew_bool; auto_tilde.
Tactic Notation "rew_bool" "*" :=
  rew_bool; auto_star.
Tactic Notation "rew_bool" "~" "in" "*":=
  rew_bool in *; auto_tilde.
Tactic Notation "rew_bool" "*" "in" "*":=
  rew_bool in *; auto_star.


(** Making definitions opaque ensures that the [simpl] tactic does
    not break symmetry in proofs. *)

Opaque and or neg.



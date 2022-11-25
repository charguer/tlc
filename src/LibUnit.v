(**************************************************************************
* Product of Data Structures                                              *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibReflect.


(* ********************************************************************** *)
(** * Unit type *)

(* ---------------------------------------------------------------------- *)
(** ** Definition *)

(** From the Prelude.

  Inductive unit : Type :=
    | tt : unit.

  Add Printing If bool.
  Delimit Scope bool_scope with bool.

*)

(* ---------------------------------------------------------------------- *)
(** ** Inhabited *)

#[global]
Instance Inhab_unit : Inhab unit.
Proof using. intros. apply (Inhab_of_val tt). Qed.


(* ********************************************************************** *)
(** * Properties *)

(* ---------------------------------------------------------------------- *)
(** ** Uniqueness *)

Lemma unit_eq : forall (tt1 tt2 : unit),
  tt1 = tt2.
Proof using. intros. destruct tt1. destruct~ tt2. Qed.




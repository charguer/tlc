(**************************************************************************
* Product of Data Structures                                              *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibReflect.


(* ********************************************************************** *)
(** * Definition  *)

(** From the Prelude. 

  Inductive unit : Type :=
    | tt : unit.

  Add Printing If bool.
  Delimit Scope bool_scope with bool.

*)


(* ********************************************************************** *)
(** * Inhabited  *)

Instance Inhab_unit : Inhab unit.
Proof using. intros. apply (Inhab_of_val tt). Qed.


(* ********************************************************************** *)
(** * Structure *)

Lemma unit_unique : forall tt1 tt2 : unit,
  tt1 = tt2.
Proof using. intros. destruct tt1. destruct~ tt2. Qed.




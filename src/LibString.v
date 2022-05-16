(**************************************************************************
* TLC: A library for Coq                                                  *
* Strings                                                                 *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics LibReflect.
Require Export Coq.Strings.String.


(* ********************************************************************** *)
(** * Inhabited *)

#[global]
Instance Inhab_string : Inhab string.
Proof using. apply (Inhab_of_val EmptyString). Qed.

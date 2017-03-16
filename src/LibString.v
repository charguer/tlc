(**************************************************************************
* TLC: A library for Coq                                                  *
* Strings                                                                 *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibReflect.
Require Export String.


(* ********************************************************************** *)
(** * Inhabited *)

Instance string_inhab : Inhab string.
Proof using. apply (Inhab_of_val EmptyString). Qed.

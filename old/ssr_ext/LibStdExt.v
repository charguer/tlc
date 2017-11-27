Require Import List.

(* Very important to remove hint trans_eq_bool from LibBool,
   otherwise eauto slows down dramatically:
  Lemma test : forall b, b = false.
  time eauto 7. (* takes over 4 seconds  to fail! *) *)

Remove Hints Bool.trans_eq_bool.

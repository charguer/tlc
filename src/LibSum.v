(**************************************************************************
* TLC: A library for Coq                                                  *
* Sum of Data Structures                                                  *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibBool.
Generalizable Variables A B.

(* ********************************************************************** *)
(** * Fixing implicit types *)

Arguments inl {A} {B}.
Arguments inr {A} {B}.


(* ********************************************************************** *)
(** * Inhabited *)

Instance sum_inhab_left : forall `{Inhab A} B, Inhab (A + B).
Proof using. intros. apply (prove_Inhab (inl arbitrary)). Qed.

Instance sum_inhab_right : forall `{Inhab B} A, Inhab (A + B).
Proof using. intros. apply (prove_Inhab (inr arbitrary)). Qed.

Definition sum_inhab : forall `{Inhab A, Inhab B}, Inhab (A + B).
Proof using. typeclass. Qed.


(* ********************************************************************** *)
(** * Operations *)

Definition is_inl (A B : Type) (x : A + B) : bool :=
  match x with
  | inl _ => true
  | inr _ => false
  end.

Definition is_inr (A B : Type) (x : A + B) : bool :=
  match x with
  | inl _ => false
  | inr _ => true
  end.


Section IsIn.
Variables (A B : Type).
Implicit Type x : A + B.

Lemma is_inl_neg_is_inr : forall x,
  is_inl x = ! (is_inr x).
Proof using. intros x. destruct~ x. Qed.

Lemma is_inr_neg_is_inl : forall x,
  is_inr x = ! (is_inl x).
Proof using. intros x. destruct~ x. Qed.

End IsIn.


(* ********************************************************************** *)
(** * Projections *)

(*-----------------------------------------------------*)
(** ** Stripping of the branch tag *)

Section Get.
Context `{IA1:Inhab A1} `{IA2:Inhab A2}.
Implicit Types x : A1+A2.

Definition get21 x :=
  match x with
  | inl x1 => x1
  | inr x2 => arbitrary
  end.

Definition get22 x :=
  match x with
  | inl x1 => arbitrary
  | inr x2 => x2
  end.

End Get.


(*-----------------------------------------------------*)
(** ** Lifting functions over sum types *)

Section Fget.
Context {A1:Type} {A2:Type} `{IB1:Inhab B1} `{IB2:Inhab B2}.
Implicit Types f : A1+A2->B1+B2.

Definition fun_get21 f :=
  fun x => get21 (f (inl x)).
Definition fun_get22 f :=
  fun x => get22 (f (inr x)).

End Fget.


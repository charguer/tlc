(**************************************************************************
* TLC: A library for Coq                                                  *
* Functions                                                               *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibBag LibSet.
Generalizable Variables A.


(* ********************************************************************** *)
(** ** Indentity function *)

Definition id {A} (x : A) := 
  x.


(* ********************************************************************** *)
(** Constant functions *)

Definition const {A B} (v : B) : A -> B := 
  fun _ => v.
Definition const1 := 
  @const.
Definition const2 {A1 A2 B} (v:B) : A1->A2->B :=
  fun _ _ => v.
Definition const3 {A1 A2 A3 B} (v:B) : A1->A2->A3->B :=
  fun _ _ _ => v.
Definition const4 {A1 A2 A3 A4 B} (v:B) : A1->A2->A3->A4->B :=
  fun _ _ _ _ => v.
Definition const5 {A1 A2 A3 A4 A5 B} (v:B) : A1->A2->A3->A4->A5->B :=
  fun _ _ _ _ _ => v.

(* ********************************************************************** *)
(** Function application *)

Definition apply {A B} (f : A -> B) (x : A) :=
  f x.

Definition apply_to (A : Type) (x : A) (B : Type) (f : A -> B) :=
  f x.


(* ********************************************************************** *)
(** Function composition *)

Definition compose {A B C} (g : B -> C) (f : A -> B) := 
  fun x => g (f x).

Notation "f1 \o f2" := (compose f1 f2) 
  (at level 49, right associativity) : func_scope.

Section Combinators.
Open Scope func_scope.
Variables (A B C D : Type).

Lemma compose_id_l : forall (f:A->B),
  id \o f = f. 
Proof using. intros. apply~ func_ext_1. Qed.

Lemma compose_id_r : forall (f:A->B),
  f \o id = f. 
Proof using. intros. apply~ func_ext_1. Qed.

Lemma compose_assoc : forall (f:C->D) (g:B->C) (h:A->B), 
  (f \o g) \o h = f \o (g \o h).
Proof using. intros. apply~ func_ext_1. Qed.

Lemma compose_eq_l : forall (f:B->C) (g1 g2:A->B),
  g1 = g2 -> f \o g1 = f \o g2.
Proof using. intros. subst~. Qed.

Lemma compose_eq_r : forall (f:A->B) (g1 g2:B->C),
  g1 = g2 -> g1 \o f = g2 \o f.
Proof using. intros. subst~. Qed.

End Combinators.

(** Tactic for simplifying function compositions *)

Hint Rewrite compose_id_l compose_id_r compose_assoc : rew_compose.
Tactic Notation "rew_compose" := 
  autorewrite with rew_compose.
Tactic Notation "rew_compose" "in" "*" := 
  autorewrite with rew_compose in *.
Tactic Notation "rew_compose" "in" hyp(H) := 
  autorewrite with rew_compose in H.


(* ********************************************************************** *)
(** ** Function update *)

(** [fupdate f a b x] is like [f] except that it returns [b] for input [a] *)

Definition fupdate A B (f : A -> B) (a : A) (b : B) : A -> B :=
  fun x => If (x = a) then b else f x.

Lemma fupdate_def : forall A B (f:A->B) a b x,
  fupdate f a b x = If (x = a) then b else f x.
Proof. auto. Qed.

Lemma fupdate_eq : forall A B (f:A->B) a b x,
  x = a ->
  fupdate f a b x = b.
Proof using. intros. unfold fupdate. case_if*. Qed.

Lemma fupdate_neq : forall A B (f:A->B) a b x,
  x <> a ->
  fupdate f a b x = f x.
Proof using. intros. unfold fupdate. case_if*. Qed.

(* Opaque fupdate. -- could be added in the future *)


(* ********************************************************************** *)
(** ** Function image *)

Section FunctionImage.
Open Scope set_scope.

Definition image A B (f : A -> B) (E : set A) : set B :=
  \set{ y | exists_ x \in E, y = f x }.  

Lemma finite_image:
  forall A B (f : A -> B) (E : set A),
  finite E ->
  finite (image f E).
Proof using.
Admitted.

Lemma image_covariant:
  forall A B (f : A -> B) (E F : set A),
  E \c F ->
  image f E \c image f F.
Proof using.
Admitted.

Lemma image_union:
  forall A B (f : A -> B) (E F : set A),
  image f (E \u F) = image f E \u image f F.
Proof using.
Admitted.

Lemma image_singleton:
  forall A B (f : A -> B) (x : A),
  image f \{x} = \{f x}.
Proof using.
Admitted.

End FunctionImage.



(* ********************************************************************** *)
(** ** Function preimage *)

Section FunctionPreimage.
Open Scope set_scope.

Definition preimage A B (f : A -> B) (E : set B) : set A :=
  \set{ x | exists_ y \in E, y = f x }.

End FunctionPreimage.

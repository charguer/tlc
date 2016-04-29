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

(** Composition of [LibList.map] behaves well. **)
(* Could not be put in [LibList] because of circular dependencies. *)
Require Import LibList.
Lemma list_map_compose : forall A B C (f : A -> B) (g : B -> C) l,
  LibList.map g (LibList.map f l) = LibList.map (g \o f) l.
Proof.
  introv. induction l.
   reflexivity.
   rew_list. fequals~.
Qed.

End Combinators.

(** Tactic for simplifying function compositions *)
(* TODO: not used; might become deprecated *)

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
Require Import LibList.

Definition image A B (f : A -> B) (E : set A) : set B :=
  \set{ y | exists_ x \in E, y = f x }.

Lemma in_image_prove_eq : forall A B x (f : A -> B) (E : set A),
  x \in E -> f x \in image f E.
Proof using. introv N. unfold image. rew_set. exists* x. Qed.

Lemma in_image_prove : forall A B x y (f : A -> B) (E : set A),
  x \in E -> y = f x -> y \in image f E.
Proof using. intros. subst. applys* in_image_prove_eq. Qed.

Lemma in_image_inv : forall A B y (f : A -> B) (E : set A),
  y \in image f E -> exists x, x \in E /\ y = f x.
Proof using. introv N. unfolds image. rew_set in N. auto. Qed.

Lemma finite_image : forall A B (f : A -> B) (E : set A),
  finite E ->
  finite (image f E).
Proof using.
  introv M. lets (L&H): finite_covers_basic M.
  applys finite_prove_covers (LibList.map f L). introv N.
  lets (y&Hy&Ey): in_image_inv (rm N). subst x. applys* Mem_map.
Qed.

Lemma image_covariant : forall A B (f : A -> B) (E F : set A),
  E \c F ->
  image f E \c image f F.
Proof using.
  introv. do 2 rewrite incl_in_eq. introv M N.
  lets (y&Hy&Ey): in_image_inv (rm N). applys* in_image_prove.
Qed.

Lemma image_union : forall A B (f : A -> B) (E F : set A),
  image f (E \u F) = image f E \u image f F.
Proof using.
  Hint Resolve in_image_prove.
  introv. apply in_extens. intros x. iff N.
    lets (y&Hy&Ey): in_image_inv (rm N). rewrite in_union_eq in Hy.
     rewrite in_union_eq. destruct* Hy.
    rewrite in_union_eq in N. destruct N as [N|N].
      lets (y&Hy&Ey): in_image_inv (rm N). applys* in_image_prove.
       rewrite in_union_eq. eauto.
      lets (y&Hy&Ey): in_image_inv (rm N). applys* in_image_prove.
       rewrite in_union_eq. eauto.
Qed.

Lemma image_singleton : forall A B (f : A -> B) (x : A),
  image f \{x} = \{f x}.
Proof using.
  intros. apply in_extens. intros z. iff N.
    lets (y&Hy&Ey): in_image_inv (rm N). rewrite in_single_eq in Hy. subst~.
    rewrite in_single_eq in N. applys* in_image_prove.
Qed.

End FunctionImage.

Hint Resolve finite_image : finite.

(* ********************************************************************** *)
(** ** Function preimage *)

Section FunctionPreimage.
Open Scope set_scope.

Definition preimage A B (f : A -> B) (E : set B) : set A :=
  \set{ x | exists_ y \in E, y = f x }.

End FunctionPreimage.



(* ********************************************************************** *)
(** ** Function iteration *)

Fixpoint applyn A n (f : A -> A) x :=
  match n with
  | O => x
  | S n' =>
    f (applyn n' f x)
  end.

Lemma applyn_fix : forall A n f (x : A),
  applyn (S n) f x = applyn n f (f x).
Proof. introv. induction~ n. simpls. rewrite~ IHn. Qed.

Lemma applyn_comp : forall A n m f (x : A),
  applyn n f (applyn m f x) = applyn (n + m) f x.
Proof.
  introv. gen m; induction n; introv; simpls~.
  rewrite~ IHn.
Qed.

Lemma applyn_nested : forall A n m f (x : A),
  applyn n (applyn m f) x = applyn (n * m) f x.
Proof.
  introv. gen m. induction n; introv; simpls~.
  rewrite IHn. rewrite~ applyn_comp.
Qed.

Lemma applyn_altern : forall A B (f : A -> B) (g : B -> A) x n,
  applyn n (fun x => f (g x)) (f x) =
    f (applyn n (fun x => g (f x)) x).
Proof. introv. gen x. induction~ n. introv. repeat rewrite applyn_fix. autos~. Qed.

Lemma applyn_ind : forall A (P : A -> Prop) (f : A -> A) x n,
  (forall x, P x -> P (f x)) ->
  P x ->
  P (applyn n f x).
Proof. introv I. induction n; introv Hx; autos*. Qed.


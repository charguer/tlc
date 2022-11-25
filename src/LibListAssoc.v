(**************************************************************************
* TLC: A library for Coq                                                  *
* Association lists                                                       *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
From TLC Require Import LibTactics LibReflect.
From TLC Require Export LibList.


(* ---------------------------------------------------------------------- *)
(* ** Association list lookup *)

Fixpoint get_opt A B (x:A) (l:list(A*B)) : option B :=
  match l with
  | nil => None
  | (y,v)::l' => If y = x
                   then Some v
                   else get_opt x l'
  end.

Section GetOpt.
Variables (A B : Type).
Implicit Types a x y : A.
Implicit Types v : B.
Implicit Types l : list (A*B).

Lemma get_opt_nil : forall a,
  get_opt a (nil:list(A*B)) = None.
Proof using. auto. Qed.

Lemma get_opt_cons : forall x v l a,
  get_opt a ((x,v)::l) = (If x = a then Some v else get_opt a l).
Proof using. auto. Qed.

Lemma get_opt_app : forall l1 l2 a,
  get_opt a (l1 ++ l2) = match get_opt a l1 with
                         | None => get_opt a l2
                         | Some v => Some v
                         end.
Proof using.
  introv. induction l1 as [|(y,w) l1']; rew_list; simpl.
  { auto. }
  { case_if*. }
Qed.

End GetOpt.

Global Opaque get_opt.

#[global]
Hint Rewrite get_opt_nil get_opt_cons get_opt_app : rew_listx.


(* ---------------------------------------------------------------------- *)
(** ** Equivalence *)

Definition equiv A B (l1 l2:list(A*B)) :=
  forall x, get_opt x l1 = get_opt x l2.

Lemma equiv_sym : forall A B (l1 l2:list (A*B)),
  equiv l1 l2 ->
  equiv l2 l1.
Proof using. introv M. intros x. rewrite* M. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Disjointness *)

Definition disjoint A B (l1 l2:list(A*B)) :=
  forall x v1 v2, get_opt x l1 = Some v1 -> get_opt x l2 = Some v2 -> False.

Section Disjoint.
Variables (A B : Type).
Implicit Types l : list (A*B).

Lemma disjoint_sym : forall l1 l2,
  disjoint l1 l2 ->
  disjoint l2 l1.
Proof using. introv M N1 N2. applys M N2 N1. Qed.

Lemma disjoint_cons_l_inv : forall x v l1 l2,
  disjoint ((x,v)::l1) l2 ->
  disjoint l1 l2.
Proof using.
  introv M. intros y v1 v2 K1 K2. tests C: (x = y).
  { applys M v v2 K2. rewrite get_opt_cons. case_if~. }
  { applys M v1 v2 K2. rewrite get_opt_cons. case_if~. }
Qed.

End Disjoint.


(* ---------------------------------------------------------------------- *)
(* ** Association list key removal *)

Definition rem A B (x:A) (l:list(A*B)) :=
  LibList.filter (fun '(y,v) => x <> y) l.

Section Rem.
Variables (A B : Type).
Implicit Types a x y : A.
Implicit Types v : B.
Implicit Types l : list (A*B).

Lemma rem_as_filter : forall a l,
  rem a l = LibList.filter (fun '(x,v) => a <> x) l.
Proof using. auto. Qed.

Lemma rem_nil : forall a,
  rem a (nil:list(A*B)) = nil.
Proof using. auto. Qed.

Lemma rem_cons : forall x v l a,
  rem a ((x,v)::l) = (If x = a then rem a l else (x,v) :: rem a l).
Proof using. intros. unfold rem. rewrite filter_cons. repeat case_if~. Qed.

Lemma rem_app : forall l1 l2 a,
  rem a (l1 ++ l2) = rem a l1 ++ rem a l2.
Proof using. intros. unfold rem. rewrite~ filter_app. Qed.

Lemma rem_last : forall x v l a,
  rem a (l & (x,v)) = rem a l ++ (If x = a then nil else (x,v)::nil).
Proof using. intros. unfold rem. rewrite filter_last. repeat case_if~. Qed.

Lemma get_opt_rem : forall x a l,
  get_opt x (rem a l) = (If x = a then None else get_opt x l).
Proof using.
  intros. induction l as [|(y,v) l']; simpl.
  { do 2 rewrite~ get_opt_nil. case_if~. }
  { rewrite rem_cons. rewrite get_opt_cons.
    case_if; try rewrite get_opt_cons; repeat case_if; auto. }
Qed.

Lemma equiv_rem : forall a l1 l2,
  equiv l1 l2 ->
  equiv (rem a l1) (rem a l2).
Proof using.
  introv M. unfolds equiv. intros y.
  do 2 rewrite get_opt_rem. case_if~.
Qed.

Lemma disjoint_rem : forall a l1 l2,
  disjoint l1 l2 ->
  disjoint (rem a l1) (rem a l2).
Proof using.
  introv D. intros y v1 v2 K1 K2. rewrite get_opt_rem in *.
  case_if~. applys* D K1 K2.
Qed.

End Rem.

#[global]
Hint Rewrite rem_nil rem_cons rem_app rem_last : rew_listx.

Global Opaque rem.


(* ---------------------------------------------------------------------- *)
(* ** Membership of keys *)

(* LATER:

Definition mem_assoc A B (x:A) (l:list (A*B)) : Prop :=
  LibList.mem x (LibList.map fst l).

*)

(* LATER: keys function *)

(* ---------------------------------------------------------------------- *)
(* ** Association list: membership as a relation *)

(** [Assoc x v l] asserts that [(x,v)] the first pair of the
    form [(x,_)] in [l] *)

Inductive Assoc A B (x:A) (v:B) : list (A*B) -> Prop :=
  | Assoc_here : forall l ,
      Assoc x v ((x,v)::l)
  | Assoc_next : forall y l w,
      Assoc x v l ->
      x <> y ->
      Assoc x v ((y,w)::l).

(* --LATER: lemmas about Assoc *)

(* LATER: relation with get_opt
  Lemma get_opt_some_eq_assoc : forall x v l,
    (get_opt x l = Some v) = Assoc x v l.
  Proof using.
  Qed.

  Lemma get_opt_some_eq_not_assoc : forall x v,
    (get_opt x l = None) = (forall v, ~ Assoc x v l).
  Proof using.
  Qed.
*)




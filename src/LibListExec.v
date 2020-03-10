(**************************************************************************
* TLC: A library for Coq                                                  *
* Executable operations for lists                                         *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
From TLC Require Import LibTactics LibReflect.
From TLC Require Export LibList.


(* ---------------------------------------------------------------------- *)
(* ** [is_nil] and [is_not_nil] *)

Definition is_nil A (l:list A) : bool :=
  match l with
  | nil => true
  | _ => false
  end.

Lemma is_nil_eq : forall A (l:list A),
  is_nil l = isTrue (l = nil).
Proof using. intros. destruct l; simpl; rew_bool_eq; auto_false. Qed.

Definition is_not_nil A (l:list A) : bool :=
  match l with
  | nil => false
  | _ => true
  end.

Lemma is_not_nil_eq : forall A (l:list A),
  is_not_nil l = isTrue (l <> nil).
Proof.
  intros. destruct l; simpl; rew_bool_eq; auto_false.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** [length] *)

Definition length : forall A, list A -> nat :=
  List.length.

Lemma length_eq :
  length = LibList.length.
Proof using. extens ;=> A l. induction l; simpl; rew_list; auto. Qed.


(* ---------------------------------------------------------------------- *)
(* ** [app] *)

Definition app : forall A, list A -> list A -> list A :=
  List.app.

Lemma app_eq :
  List.app = LibList.app.
Proof using.
  extens ;=> A L1 L2. induction L1; simpl; rew_list; congruence.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** [rev] *)

Definition rev : forall A, list A -> list A :=
  List.rev.

Lemma List_rev_eq : forall A, (* --LATER: why fails if A is not quantified here? *)
  @List.rev A = @LibList.rev A.
Proof using.
  extens ;=> L. induction L; simpl; rew_list. { auto. }
  { rewrite app_eq. simpl. congruence. }
Qed.


(* ---------------------------------------------------------------------- *)
(* ** [fold_right] *)

Definition fold_right : forall A B, (B->A->A) -> A -> list B -> A :=
  List.fold_right.

Lemma List_fold_right_eq : forall A B (f:B->A->A) (a:A) (l:list B),
  fold_right f a l = LibList.fold_right f a l.
Proof using. intros. induction l; simpl; rew_listx; fequals. Qed.


(* ---------------------------------------------------------------------- *)
(* ** [map] *)

Definition map : forall A B, (A->B) -> list A -> list B :=
  List.map.

Lemma List_map_eq :
  List.map = LibList.map.
Proof using.
  extens ;=> A B f L. induction L; simpl; rew_listx; congruence.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** [combine] *)

Definition combine : forall A B, list A -> list B -> list (A*B) :=
  List.combine.

Lemma combine_eq : forall A B (L1:list A) (L2:list B),
  LibList.length L1 = LibList.length L2 ->
  combine L1 L2 = LibList.combine L1 L2.
Proof using. (* --LATER: conduct proof using list2_ind *)
  introv E. gen L2.
  induction L1 as [|x1 L1']; intros; destruct L2 as [|x2 L2']; tryfalse.
  { auto. }
  { rew_list in E. rew_listx. simpl. fequals~. }
Qed.

(* ---------------------------------------------------------------------- *)
(* ** [mem] *)

Fixpoint mem A (cmp:A->A->bool) (x:A) (l:list A) : bool :=
  match l with
  | nil => false
  | y::l' => cmp x y || mem cmp x l'
  end.

Lemma mem_exec_eq : forall A (cmp:A->A->bool) x l,
  is_beq cmp ->
  mem cmp x l = isTrue (LibList.mem x l).
Proof using.
  introv M. induction l as [|y l']; simpl; rew_listx; rew_isTrue; fequals.
Qed.


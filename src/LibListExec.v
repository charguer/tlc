(**************************************************************************
* TLC: A library for Coq                                                  *
* Executable operations for lists                                         *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
From TLC Require Import LibTactics LibReflect.
From TLC Require Export LibNat LibList.

(** This module shadows the function from LibList. Hence, it is not meant
    to be "imported". Instead, just use [Import LibListExec.RewListExec.] *)

(* ---------------------------------------------------------------------- *)
(* ** Autorewrite *)

Module Import RewListExec.

Tactic Notation "rew_list_exec" :=
  autorewrite with rew_list_exec.
Tactic Notation "rew_list_exec" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_list_exec).
  (* autorewrite with rew_list_exec in *. *)
Tactic Notation "rew_list_exec" "in" hyp(H) :=
  autorewrite with rew_list_exec in H.

End RewListExec.


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

#[global] Hint Rewrite is_nil_eq is_not_nil_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(* ** [length] *)

Definition length : forall A, list A -> nat :=
  @List.length.

Lemma length_eq :
  length = LibList.length.
Proof using. extens ;=> A l. induction l; simpl; rew_list; auto. Qed.

#[global] Hint Rewrite length_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(* ** [app] *)

Definition app : forall A, list A -> list A -> list A :=
  @List.app.

Lemma app_eq :
  app = LibList.app.
Proof using.
  extens ;=> A L1 L2. induction L1; simpl; rew_list; congruence.
Qed.

#[global] Hint Rewrite app_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(* ** [rev] *)

Definition rev : forall A, list A -> list A :=
  @List.rev.

Lemma rev_eq : forall A, (* --LATER: why fails if A is not quantified here? *)
  @List.rev A = @LibList.rev A.
Proof using.
  extens ;=> L. induction L; simpl; rew_list. { auto. }
  { rewrite IHL. rewrite <- app_eq. unfold app. fequals. }
Qed.

#[global] Hint Rewrite rev_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(* ** [map] *)

Definition map : forall A B, (A->B) -> list A -> list B :=
  @List.map.

Lemma map_eq :
  map = LibList.map.
Proof using.
  extens ;=> A B f L. induction L; simpl; rew_listx; congruence.
Qed.

#[global] Hint Rewrite map_eq : rew_list_exec.

(* ---------------------------------------------------------------------- *)
(* ** [mem] *)

Fixpoint mem A (cmp:A->A->bool) (x:A) (l:list A) : bool :=
  match l with
  | nil => false
  | y::l' => cmp x y || mem cmp x l'
  end.

Lemma mem_eq : forall A (cmp:A->A->bool) x l,
  is_beq cmp ->
  mem cmp x l = isTrue (LibList.mem x l).
Proof using.
  introv M. induction l as [|y l']; simpl; rew_listx; rew_isTrue; fequals.
Qed.

#[global] Hint Rewrite mem_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(** ** [concat] *)

Definition concat A (m:list (list A)) : list A :=
  fold_right (@app A) (@nil A) m.

Transparent LibList.concat.
Lemma concat_eq :
  concat = LibList.concat.
Proof using.
  unfold concat. rew_list_exec. unfold LibList.concat. rew_list_exec. auto.
Qed.

#[global] Hint Rewrite concat_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(** ** [filter] *)

Definition filter A (p:A->bool) (l:list A) : list A :=
  fold_right (fun x acc => if p x then x::acc else acc) (@nil A) l.

Lemma filter_eq : forall A (p:A->bool) (P:A->Prop) l,
  isTrue_pred p P ->
  filter p l = LibList.filter P l.
Proof using.
  Local Transparent LibList.filter.
  introv E. unfold filter, LibList.filter. rew_list_exec.
  fequals. extens. intros. rewrite E. rewrite* if_isTrue.
Qed.

#[global] Hint Rewrite filter_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(** ** [remove] *)

Definition remove A (cmp:A->A->bool) (a:A) (l:list A) : list A :=
  filter (fun x => neg (cmp a x)) l.

Lemma remove_eq : forall A (cmp:A->A->bool) (a:A) (l:list A),
  is_beq cmp ->
  remove cmp a l = LibList.remove a l.
Proof using.
  Local Transparent LibList.remove.
  introv E. unfold remove, LibList.remove.
  rewrites* (>> filter_eq (<> a)).
  { intros x. rewrite E. rew_isTrue. fequals. rew_bool_eq*. }
Qed.

#[global] Hint Rewrite remove_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(* ** [noduplicates] *)

Fixpoint noduplicates A (cmp:A->A->bool) (l:list A) : bool :=
  match l with
  | nil => true
  | x::l' => neg (mem cmp x l') && noduplicates cmp l'
  end.

Lemma noduplicates_eq : forall A (cmp:A->A->bool) (l:list A),
  is_beq cmp ->
  noduplicates cmp l = isTrue (LibList.noduplicates l).
Proof using.
  introv E. extens. induction l as [|x l']; simpl; rew_listx; rew_bool_eq in *.
  { autos*. }
  { rewrite* mem_eq. rew_bool_eq. iff (M1&M2); splits*. }
Qed.

#[global] Hint Rewrite noduplicates_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(* ** [remove_duplicates] *)

Fixpoint remove_duplicates A (cmp:A->A->bool) (l:list A) : list A :=
  match l with
  | nil => nil
  | x::l' => x :: (remove cmp x (remove_duplicates cmp l'))
  end.

Lemma remove_duplicates_eq : forall A (cmp:A->A->bool) (l:list A),
  is_beq cmp ->
  remove_duplicates cmp l = LibList.remove_duplicates l.
Proof using.
  Local Transparent LibList.remove_duplicates.
  introv E. induction l as [|x l']; simpl; fequals.
  rewrite* remove_eq. congruence.
Qed.

#[global] Hint Rewrite remove_duplicates_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(* ** [Forall] *)

Fixpoint Forall A (p:A->bool) (l:list A) : bool :=
  match l with
  | nil => true
  | x::l' => p x && Forall p l'
  end.

Lemma Forall_eq : forall A (p:A->bool) (P:A->Prop) l,
  isTrue_pred p P ->
  Forall p l = isTrue (LibList.Forall P l).
Proof using.
  introv E. extens. induction l as [|x l']; simpl; rew_listx in *; rew_bool_eq in *.
  { iff*. }
  { rewrite E. rew_bool_eq. iff*. }
Qed.

#[global] Hint Rewrite Forall_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(* ** [Exists] *)

Fixpoint Exists A (p:A->bool) (l:list A) : bool :=
  match l with
  | nil => false
  | x::l' => p x || Exists p l'
  end.

Lemma Exists_eq : forall A (p:A->bool) (P:A->Prop) l,
  isTrue_pred p P ->
  Exists p l = isTrue (LibList.Exists P l).
Proof using.
  introv E. extens. induction l as [|x l']; simpl; rew_listx in *; rew_bool_eq in *.
  { iff*. }
  { rewrite E. rew_bool_eq. iff*. }
Qed.

#[global] Hint Rewrite Exists_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(* ** [Count] *)

Fixpoint count A (p:A->bool) (l:list A) : nat :=
  match l with
  | nil => 0%nat
  | x::l' => if p x then S (count p l') else count p l'
  end.

Lemma count_eq : forall A (p:A->bool) (P:A->Prop) l,
  isTrue_pred p P ->
  count p l = LibList.count P l.
Proof using.
  introv E. induction l as [|x l']; simpl; rew_listx.
  { auto. }
  { rewrite IHl'. rewrite E. do 2 case_if; try nat_math. }
Qed.

#[global] Hint Rewrite count_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(* ** [combine] *)

Definition combine : forall A B, list A -> list B -> list (A*B) :=
  @List.combine.

Lemma combine_eq : forall A B (L1:list A) (L2:list B),
  LibList.length L1 = LibList.length L2 ->
  combine L1 L2 = LibList.combine L1 L2.
Proof using. (* --LATER: conduct proof using list2_ind *)
  introv E. gen L2.
  induction L1 as [|x1 L1']; intros; destruct L2 as [|x2 L2']; tryfalse.
  { auto. }
  { rew_list in E. rew_listx. simpl. fequals~. }
Qed.

#[global] Hint Rewrite combine_eq : rew_list_exec.


(* ---------------------------------------------------------------------- *)
(* ** [fold_right] *)

(** [LibList.fold_right] computes well. Here, we prove that it matches
    Coq's standard library [fold_right]. *)

Lemma fold_right_eq : forall A B,
  @List.fold_right B A = @LibList.fold_right A B.
Proof using. extens. intros a b l. induction l; simpl; rew_listx; fequals. Qed.

#[global] Hint Rewrite fold_right_eq : rew_list_exec.



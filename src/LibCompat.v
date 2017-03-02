
(**************************************************************************
* TLC: A library for Coq                                                  *
* Compatibility with Coq stdlib                                           *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import LibList.



(* ********************************************************************** *)
(** Lists *)


(* The head of a list is its first element. *)

Definition head (xs : list A) : option A :=
  match xs with
  | nil => None
  | x :: _ => Some x
  end.

(* The tail of a list is everything beyond its first element. *)

Definition tail (xs : list A) : list A :=
  match xs with
  | nil => nil
  | _ :: xs => xs
  end.

(* No list is cyclic. *)

Lemma no_cyclic_list:
  forall (xs : list A) x,
  x :: xs = xs ->
  False.
Proof using.
  induction xs; simpl; introv h.
  { congruence. }
  { injection h. clear h. intros h ?. subst x. eauto. }
Qed.

(* Only the empty list is its own tail. *)

Lemma tail_self_inv:
  forall (xs : list A),
  tail xs = xs ->
  xs = nil.
Proof using.
  destruct xs; simpl; intros.
  { eauto. }
  { false. eauto using no_cyclic_list. }
Qed.


(* Equivalence. *)

Lemma head_hd_error (xs : list A) : head xs = List.hd_error xs.
Proof. destruct xs; reflexivity. Qed.

Lemma tail_tl (xs : list A) : tail xs = List.tl xs.
Proof. destruct xs; reflexivity. Qed.


(* ********************************************************************** *)
(** Lemmas about [head] *)

(* The empty list, and only the empty list, has no head. *)

Lemma use_None_head (xs : list A) : None = head xs -> xs = nil.
Proof. destruct xs; simpl; congruence. Qed.

Lemma use_Some_head x (xs : list A) : Some x = head xs -> xs <> nil.
Proof. destruct xs; simpl; congruence. Qed.



(* ********************************************************************** *)
(** Renamings *)

(* DEPRECATED: now [fold_right_rev] *)
Lemma fold_left_eq_fold_right_rev : forall B (f : A -> B -> B) i l,
  fold_left f i l = fold_right f i (rev l).
Proof using. introv. gen i. induction~ l. introv. rewrite rev_cons. rewrite* fold_right_last. Qed.

Definition nil_map := map_eq_nil.

Definition map_mem := mem_map.

(* NOW formulated differently *)
Lemma split_cons : forall {A1 A2}
 (l1:list A1) (l2:list A2) (x1:A1) (x2:A2) (l:list (A1*A2)),
  (l1,l2) = split l ->
  split ((x1,x2)::l) = (x1::l1,x2::l2).
Proof using.
  intros. destruct l; inverts H; simpl.
    auto.
    destruct p. simpl. destruct (split l). fequals.
Qed.



Arguments length_zero_inv [A] [l].

Lemma cons_make: forall n (x : A),
  0 < n ->
  x :: make (n - 1) x = make n x.
Proof.
  induction n; intros; simpl.
  { math. }
  { rewrite <- minus_n_O. eauto. }
Qed.



Definition last_inv := last_inv_pos_length.


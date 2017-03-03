
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

(* Replaced with rev_mem *)
Lemma rev_mem : forall l x,
  mem x l = mem x (rev l).
Proof using.
  introv. induction~ l. rewrite mem_cons. rewrite rev_cons.
  rewrite mem_last. extens. rew_refl. rewrite* IHl.
Qed.

(* replaced with Mem_concat *)
Lemma concat_mem : forall Ls x,
      mem x (concat Ls)
  <-> exists L, mem L Ls /\ mem x L.
Proof using.
  introv. induction Ls.
   simpl. iff I; inverts* I.
  rewrite concat_cons. iff I.
   rewrite mem_app in I. rew_refl in *. inverts I as I.
    exists a. splits~. rewrite mem_cons. rew_refl*.
    apply IHLs in I. lets (l&Il&Ix): (rm I).
     exists l. rewrite mem_cons. rew_refl*.
   rewrite mem_app. rew_refl. lets (l&Il&Ix): (rm I).
    rewrite mem_cons in Il. rew_refl in Il. inverts Il as Il.
     left~.
     right~. apply* IHLs.
Qed.

Definition app_cons := app_cons_l.
Definition app_last := app_cons_r.
Definition app_last_sym := app_last_l.

(* [fold_left_app] is no longer in [rew_list] *)

(* simulate with [rew_list] using [rev_cons] and [app_cons_r] *)
Lemma rev_cons_app : forall x l1 l2,
  rev (x :: l1) ++ l2 = rev l1 ++ (x::l2).
Proof using. intros. rewrite rev_cons. rew_list~. Qed.

(* idem *)
Lemma app_rev_cons : forall x l1 l2,
  l1 ++ rev (x :: l2) = (l1 ++ rev l2) & x.
Proof using. intros. rewrite rev_cons. rewrite~ app_assoc. Qed.

Definition map_eq_nil := map_eq_nil_inv.

(* use Mem_map *)
Lemma map_mem : forall f l (x : B),
  mem x (map f l) <->
    exists y, mem y l /\ x = f y.
Proof using. (* TODO: simplify proof *)
  induction l; introv.
   simpl. iff I; false*. inverts* I.
   rewrite map_cons. iff I.
     rewrite mem_cons in I. rew_refl in I. inverts I as I.
     exists a. splits~. rewrite mem_cons in *. rew_refl. left~.
     apply IHl in I. lets (y&Iy&E): (rm I). exists y. splits~.
      rewrite mem_cons. rew_refl. right~.
    lets (y&Iy&E): (rm I). substs. rewrite mem_cons in *. rew_refl in *.
     inverts Iy as I. left~.
     right. apply IHl. exists~ y.
Qed.

Definition filter_mem_eq := mem_filter.

Definition for_all := forall_bool.
Definition exists_st := exists_bool.

Definition take_nil := take_zero.


Definition take_app_length := take_prefix_length.
Definition take_at_length := take_full_length.

Definition take_and_drop := take_and_drop_struct.

(* use [rew_listx] instead of [rew_list] for [map] and [concat] *)

Definition update_cons := update_cons_match.

Definition update_cons_zero := update_zero.

Definition update_cons_succ := update_succ.
Definition take_cons_pred := take_cons_pos.

Lemma update_app_right := update_app_r. (* reformulated *)
Lemma update_app_right_here := update_prefix_length. (* reformulated *)


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



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

(* ********************************************************************** *)

Definition last_neq_nil := last_neq_nil_inv.
Lemma cons_neq_nil : forall x l,
  x::l <> nil.
Proof using. auto_false. Qed.


Definition app_cancel_nil_l := app_eq_self_inv_l

Definition app_eq_prefix_inv_l := app_cancel_l. (* DEPRECATED *) 

Definition length_neq_elim := length_neq_inv.


Definition last_inv_pos_length := length_pos_inv_last

Definition nil_eq_last_val_app_inv := nil_eq_middle_inv.

Definition cons_eq_last_val_app_inv := cons_eq_middle_inv.

Definition last_neq_nil_inv := list_neq_nil_inv_last.

Definition concat_eq_nil := concat_eq_nil_mem_inv.

Definition Update_here := udpate_zero.

Definition Update_not_nil := Update_not_nil_r.

Definition Mem := mem.
Definition mem := memb.
(* and same for all associated lemmas *)

Definition Filter := filter.
Definition filter := filterb.
(* and same for all associated lemmas *)

Definition No_duplicates := noduplicates.
(* and same for all associated lemmas *)



Definition mem_app_or := mem_app.

Definition concat_mem := mem_concat_iff.

Definition mem_inv := mem_cons_inv.

Definition nil_mem := list_no_mem.

Definition No_duplicates_inv_app := No_duplicates_app_inv.

Definition No_duplicates_Nth := No_duplicates_Nth_same_inv.

Definition Nth_No_duplicates := No_duplicates_Nth_same.

Definition Nth_lt_length := Nth_inbound.

Definition length_Nth_lt := Nth_inbound_inv.

Definition Nth_cons_inv := Nth_inv_cons.

(* See: Nth_cons_inv *)
Lemma Nth_inv_cons : forall n x l,
  Nth n l x ->
     (exists q, l = x::q /\ n = 0%nat)
  \/ (exists y q m, l = y::q /\ Nth m q x /\ n = (m+1)%nat).
Proof using.
  introv H. inverts H. left*.
  right. eauto 8 with maths.
Qed.

Definition nth_def_if_in_length := nth_def_to_Nth. (* arguments swapped *)

(** too specific *)
Lemma Forall2_Nth_nth_def : forall A B (P : A -> B -> Prop) la lb n v d,
  Forall2 P la lb ->
  Nth n la v ->
  Nth n lb (nth_def d n lb).
Proof using.
  introv F N. forwards L: Forall2_length F. forwards I: Nth_lt_length N.
  rewrite L in I. forwards*: nth_def_if_in_length I.
Qed.

Definition filter_Mem := mem_filter.

Definition filter_Mem_inv := mem_filter_inv.

Definition filter_length_le := length_filter.

Definition filter_eq_Mem_length := length_filter_mem_ge_one.

Definition filter_No_duplicates := No_duplicates_filter.

Definition filter_disjoint_predicates_length := filter_length_two_disjoint.

Definition filter_negated_predicates_length := filter_length_partition.

Definition mem_filter_neq_inv := mem_remove_inv.

Definition filter_neq_Mem_length := length_remove_mem.

Definition remove_duplicates_mem := mem_remove_duplicates.

Definition take_and_drop_struct := take_app_drop.



Definition Forall_inv_tail := Forall_cons_inv_head.
Definition Forall_inv_head := Forall_cons_inv_tail.
Definition Forall_inv := Forall_cons_inv.

Definition Forall_mem := Forall_mem_inv.


Definition Forall_iff_forall_mem := Forall_extens.

Definition Forall2_inv_length := Forall2_length.
Definition Forall2_map := Forall2_map_r.


Implicit Arguments Forall2_last_inv [A1 A2 P l1 r' x1].

Lemma Forall2_forall_Nth : forall A B (P : A -> B -> Prop) la lb,
  Forall2 P la lb -> forall n a b,
    Nth n la a ->
    Nth n lb b ->
    P a b.
Proof using. introv F N1 N2. gen n. induction~ F; introv N1 N2; inverts N1; inverts* N2. Qed.
(* => reformulated ad Forall2_inv_Nth *)

Definition Forall2_last_inv := Forall2_last_l_inv.


(* ********************************************************************** *)
(** too specific *)

(* ** Function for mapping partial function on lists *)

Definition map_partial (A B : Type) (f : A -> option B) :=
  fix aux (l : list A) : option (list B) := match l with
    | nil => Some nil
    | x::l' => LibOption.apply_on (f x) (fun v =>
                 LibOption.map (cons v) (aux l'))
   end.


Lemma map_partial_inv_none : forall (A B:Type) (f: A->option B) l,
  map_partial f l = None ->
  Exists (fun x => f x = None) l.
Proof using.
  induction l; simpl map_partial; introv Eq; tryfalse.
  forwards [E|(b&E1&E2)]: apply_on_inv_none Eq.
   apply* Exists_here.
   apply Exists_next. apply~ IHl. destruct~ map_partial. false*.
Qed.

Lemma map_partial_none : forall (A B:Type) (f: A->option B) l,
  Exists (fun x => f x = None) l ->
  map_partial f l = None.
Proof using.
  induction l; simpl map_partial; introv Eq; inverts Eq as Eq.
   rewrite~ Eq.
   destruct~ (f a). rewrite~ IHl.
Qed.

Lemma map_partial_inv : forall (A B:Type) (f: A->option B) lx ly,
  map_partial f lx = Some ly ->
  Forall2 (fun x y => f x = Some y) lx ly.
Proof using.
  induction lx; simpl map_partial; introv Eq.
   inverts Eq. apply Forall2_nil.
   lets fa Fa Eq2: (apply_on_inv Eq).
    lets ly1 Eqly ?: (map_on_inv Eq2). subst ly.
    apply* Forall2_cons.
Qed.

Implicit Arguments map_partial_inv [A B f lx ly].


(* ********************************************************************** *)

(** too specific *)

(** [has pair x1 x2 l1 l2] asserts that there exists an
    index [n] such that the n-th element of [l1] is [x1]
    and the n-th element of [l2] is [x2] *)

Definition has_pair A1 A2 (x1:A1) (x2:A2) l1 l2 :=
  Exists2 (fun v1 v2 => v1 = x1 /\ v2 = x2) l1 l2.

Lemma has_pair_here : forall A1 A2 (x1:A1) (x2:A2) l1 l2,
  has_pair x1 x2 (x1::l1) (x2::l2).
Proof using. intros. constructor~. Qed.

Lemma has_pair_next : forall A1 A2 (x1:A1) (x2:A2) y1 y2 l1 l2,
  has_pair x1 x2 l1 l2 ->
  has_pair x1 x2 (y1::l1) (y2::l2).
Proof using. introv H. apply* Exists2_next. Qed.

Hint Resolve has_pair_here has_pair_next.


(* ********************************************************************** *)


(** [filters P L L'] asserts that [L'] is the sublist of [L]
    made exactly of the elements of [L] that satisfy [P]. *)
   (* DEPRECATED: use Filter instead *)

Inductive Filters A (P : A -> Prop)
  : list A -> list A -> Prop :=
  | Filters_nil : Filters P nil nil
  | Filters_cons_yes : forall l l' x,
      P x -> Filters P l l' ->
      Filters P (x::l) (x::l')
  | Filters_cons_no : forall l l' x,
      ~ (P x) -> Filters P l l' ->
      Filters P (x::l) l'.



(* ********************************************************************** *)

(* todo: use [suffix] instead (to be defined) *)
(* todo: use [prefix] instead *)

Definition is_head A (l:list A) (x:A) :=
  exists t, l = x::t.

Definition is_tail A (l:list A) (t:list A) :=
  exists x, l = x::t.

Definition is_last A (l:list A) (x:A) :=
  exists t, l = t&x.

Definition is_init A (l:list A) (t:list A) :=
  exists x, l = t&x.

Hint Unfold is_head is_tail is_last is_init.

Section IsProp.
Variables A : Type.
Implicit Types x : A.

Lemma is_last_one : forall x,
  is_last (x::nil) x.
Proof using. intros. unfolds. exists~ (@nil A). Qed.


Lemma is_init_one : forall x,
  is_init (x::nil) nil.
Proof using. intros. unfolds. exists~ x. Qed.

End IsProp.

Hint Immediate is_last_one.
Hint Immediate is_init_one.




(* ********************************************************************** *)
(* * Tactics for rewriting *)

Hint Rewrite app_cons app_nil_l app_nil_r app_assoc
 app_cons_one : rew_app. (* app_last *)
Hint Rewrite fold_right_nil fold_right_cons fold_right_app
 fold_right_last : rew_foldr.
Hint Rewrite fold_left_nil fold_left_cons fold_left_app
 fold_left_last : rew_foldl.
Hint Rewrite length_nil length_cons length_app
 length_last length_rev : rew_length.
Hint Rewrite rev_nil rev_app rev_cons rev_last rev_rev : rew_rev.
 (* +rev_cons_app *)
Hint Rewrite concat_nil concat_app concat_cons concat_last : rew_concat.
Hint Rewrite map_nil map_cons map_app map_last : rew_map.
Hint Rewrite mem_nil mem_cons mem_app mem_last
 mem_cons_eq mem_last_eq : rew_mem.
Hint Rewrite keys_nil keys_cons keys_app keys_last : rew_keys.
Hint Rewrite assoc_cons assoc_here : rew_assoc.

(* TODO: rew_tactics other than [rew_app] and [rew_length]
   will become deprecated; use [rew_list] instead. *)

Tactic Notation "rew_app" :=
  autorewrite with rew_app.
Tactic Notation "rew_foldr" :=
  autorewrite with rew_foldr rew_app.
Tactic Notation "rew_foldl" :=
  autorewrite with rew_foldl rew_app.
Tactic Notation "rew_length" :=
  autorewrite with rew_length.
Tactic Notation "rew_rev" :=
  autorewrite with rew_rev rew_app.
Tactic Notation "rew_concat" :=
  autorewrite with rew_concat rew_app.
Tactic Notation "rew_map" :=
  autorewrite with rew_map rew_app.
Tactic Notation "rew_mem" :=
  autorewrite with rew_mem rew_app.
Tactic Notation "rew_keys" :=
  autorewrite with rew_keys rew_app.
Tactic Notation "rew_assoc" :=
  autorewrite with rew_assoc rew_app.

Tactic Notation "rew_app" "in" hyp(H) :=
  autorewrite with rew_app in H.
Tactic Notation "rew_foldr" "in" hyp(H) :=
  autorewrite with rew_foldr rew_app in H.
Tactic Notation "rew_foldl" "in" hyp(H) :=
  autorewrite with rew_foldl rew_app in H.
Tactic Notation "rew_length" "in" hyp(H) :=
  autorewrite with rew_length in H.
Tactic Notation "rew_rev" "in" hyp(H) :=
  autorewrite with rew_rev rew_app in H.
Tactic Notation "rew_concat" "in" hyp(H) :=
  autorewrite with rew_concat rew_app in H.
Tactic Notation "rew_map" "in" hyp(H) :=
  autorewrite with rew_map rew_app in H.
Tactic Notation "rew_mem" "in" hyp(H) :=
  autorewrite with rew_mem rew_app in H.
Tactic Notation "rew_keys" "in" hyp(H) :=
  autorewrite with rew_keys rew_app in H.
Tactic Notation "rew_assoc" "in" hyp(H) :=
  autorewrite with rew_assoc rew_app in H.

Tactic Notation "rew_app" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_app).
  (* autorewrite with rew_app in *. *)

  (* TODO: if those are kept, need the efficiency workaround *)
Tactic Notation "rew_foldr" "in" "*" :=
  autorewrite with rew_foldr rew_app in *.
Tactic Notation "rew_foldl" "in" "*" :=
  autorewrite with rew_foldl rew_app in *.
Tactic Notation "rew_length" "in" "*" :=
  autorewrite with rew_length in *.
Tactic Notation "rew_rev" "in" "*" :=
  autorewrite with rew_rev rew_app in *.
Tactic Notation "rew_concat" "in" "*" :=
  autorewrite with rew_concat rew_app in *.
Tactic Notation "rew_map" "in" "*" :=
  autorewrite with rew_map rew_app in *.
Tactic Notation "rew_mem" "in" "*" :=
  autorewrite with rew_mem rew_app in *.
Tactic Notation "rew_keys" "in" "*" :=
  autorewrite with rew_keys rew_app in *.
Tactic Notation "rew_assoc" "in" "*" :=
  autorewrite with rew_assoc rew_app in *.

Tactic Notation "rew_app" "~" :=
  rew_app; auto_tilde.
Tactic Notation "rew_rev" "~" :=
  rew_rev; auto_tilde.
Tactic Notation "rew_mem" "~" :=
  rew_mem; auto_tilde.
Tactic Notation "rew_length" "~" :=
  rew_length; auto_tilde.

Hint Rewrite app_cons app_nil_l app_nil_r app_assoc
 app_cons_one
 fold_right_nil fold_right_cons fold_right_app
 fold_right_last
 fold_left_nil fold_left_cons fold_left_app
 fold_left_last
 length_nil length_cons length_app length_rev
 length_last
 rev_nil rev_app rev_cons rev_last rev_rev
 concat_nil concat_app concat_cons concat_last
  map_nil map_cons map_app map_last : rew_list.


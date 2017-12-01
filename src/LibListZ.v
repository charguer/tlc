(**************************************************************************
* TLC: A library for Coq                                                  *
* Lists accessed with integers (not nat), using LibContainer typeclasses  *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
From TLC Require Import LibTactics LibLogic LibOperation LibReflect
  LibProd LibNat LibInt LibOption LibWf.
From TLC Require Export LibList LibNat.
From TLC Require Import LibInt.
From TLC Require Export LibContainer.

Local Open Scope comp_scope.

Ltac auto_tilde ::= eauto with maths.


(* ********************************************************************** *)
(** * List operations using indices in Z *)
 
(* ---------------------------------------------------------------------- *)
(** * Length, with result as [int] *)

(** Defined using a coercion from [nat] to [int] *)

Definition length A (l:list A) : int :=
  LibList.length l.

Section Length.
Variables A : Type.
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types i : int.

Lemma length_eq : forall l,
  length l = LibList.length l.
Proof using. auto. Qed.

Lemma abs_length : forall i l,
  i = length l ->
  abs i = LibList.length l.
Proof using.
  introv E. unfold length in E.
  applys eq_nat_of_eq_int.
  rewrite abs_nonneg; math.
Qed.

Lemma length_nonneg : forall (l: list A), 
  0 <= length l.
Proof using. intros. rewrite length_eq. math. Qed.

Lemma length_nil :
  length (@nil A) = 0.
Proof using. auto. Qed.

Lemma length_cons : forall x l,
  length (x::l) = 1 + length l.
Proof using. intros. unfold length. rew_list~. Qed.

Lemma length_one: forall x,
  length (x::nil) = 1.
Proof using. reflexivity. Qed.

Lemma length_app : forall l1 l2,
  length (l1 ++ l2) = length l1 + length l2.
Proof using. intros. unfold length. rew_list~. Qed.

Lemma length_last : forall x l,
  length (l & x) = 1 + length l.
Proof using. intros. unfold length. rew_list~. Qed.

Lemma length_zero_inv : forall l,
  length l = 0 -> 
  l = nil.
Proof using. intros. unfolds length. applys~ LibList.length_zero_inv. Qed.

End Length.

Hint Rewrite length_nil length_cons length_app
 length_last length_rev : rew_list.
 (* --TODO: should we use a separate [rew_listZ] data base? probably so *)

(** Automation for [math], to unfold [length] *)

Hint Rewrite length_eq : rew_maths.


(** Demo of automation with maths *)

Goal forall A (l : list A), 0 <= length l.
Proof using. intros. math. Qed.

Goal forall (l : list Z) (s n : int), 
  s <= n -> 
  s = length l -> 
  n >= 0.
Proof using. intros. math. Qed.


(* ---------------------------------------------------------------------- *)
(** * [index], with length as [int], as typeclass *)

Definition index_impl A (l:list A) (i:int) : Prop :=
  index (LibList.length l : int) i.

Instance index_inst : forall A, BagIndex int (list A).
Proof using. constructor. rapply (@index_impl A). Defined.

Section Index.
Variables (A : Type).
Implicit Types l : list A.
Implicit Types n i : int.

Lemma index_eq_inbound : forall l i,
  index l i = (0 <= i < length l).
Proof using. auto. Qed.

Lemma index_of_inbound : forall l i,
  0 <= i < length l -> 
  index l i.
Proof using. intros. rewrite~ index_eq_inbound. Qed.

Lemma index_eq_index_length : forall l i,
  index l i = index (length l) i.
Proof using. auto. Qed.

Lemma index_of_index_length : forall l i,
  index (length l) i -> 
  index l i.
Proof using. introv H. rewrite* index_eq_index_length. Qed.

(** Reformulation of above, helpful for automation *)

Lemma index_of_index_length' : forall l n i,
  index n i -> 
  n = length l -> 
  index l i.
Proof using. intros. subst. rewrite~ index_eq_index_length. Qed.

End Index.

Global Opaque index_inst.


(* ---------------------------------------------------------------------- *)
(** * [read], with length as [int], as typeclass *)

Definition read_impl `{Inhab A} (l:list A) (i:int) : A :=
  If i < 0 then arbitrary else nth (abs i) l.

Instance read_inst : forall `{Inhab A}, BagRead int A (list A).
Proof using. constructor. rapply (@read_impl A H). Defined.

Section Read.
Context (A : Type) `{Inhab A}.
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types n i : int.

Lemma read_cons_case : forall l i v,
  (v::l)[i] = (If i = 0 then v else l[i-1]).
Proof using.
  introv. simpl. unfold read_impl. case_if.
  { case_if. math. case_if~. math. }
  { case_if~.
    { subst. rewrite abs_0. rew_listx~. }
    { rewrite~ abs_eq_succ_abs_minus_one. rew_listx.
      case_if. math. auto. } }
Qed.

Lemma read_zero : forall x l,
  (x::l)[0] = x.
Proof using. 
  intros. rewrite read_cons_case. case_if. auto. 
Qed.

Lemma read_succ : forall x l i,
  0 <= i < length l ->
  (x::l)[i+1] = l[i].
Proof using.
  introv M. rewrite read_cons_case. case_if. { math. }  
  fequals. math.
Qed.

Lemma read_last_case : forall l i v,
  (l & v)[i] = (If i = length l then v else l[i]).
Proof using.
  introv. simpl. unfold read_impl. case_if.
  { case_if~; math. } 
  { rewrite nth_last_case. rewrite~ abs_eq_nat_eq. }
Qed.

Lemma read_middle : forall i l1 l2 x,
  i = length l1 ->
  (l1 ++ x :: l2)[i] = x.
Proof.
  introv M. rewrite length_eq in M. unfold read, read_inst, read_impl.
  case_if. { false; math. }
  rewrite~ nth_middle. subst. rewrite~ abs_nat.
Qed.

Lemma read_app : forall i l1 l2,
  (l1 ++ l2)[i] = (If i < length l1 then l1[i] else l2[i - length l1]).
Proof using.
  intros. rewrite length_eq. unfold read, read_inst, read_impl. case_if.
  { case_if. { auto. } { false; math. } }
  case_if as C'.
  { applys nth_app_l. applys lt_nat_of_lt_int. rewrite abs_nonneg; math. }
  case_if. { false; math. }
  rewrite abs_gt_minus_nat; [|math]. applys nth_app_r.
  { applys ge_nat_of_ge_int. rewrite abs_nonneg; math. }
Qed.

(** * Equality between two lists from equality of length and 
      extensional equality of reads. *)

Lemma eq_of_extens_range : forall l1 l2,
  length l1 = length l2 ->
  (forall i, 0 <= i < length l1 -> l1[i] = l2[i]) ->
  l1 = l2.
Proof using.
  introv HL HR. do 2 rewrite length_eq in HL.
  unfold read, read_inst, read_impl in HR.
  applys~ LibList.eq_of_extens l1 l2.
  { intros n L. forwards M: (rm HR) (nat_to_Z n). math.
    case_if. false; math. rewrite~ abs_nat in M. }
Qed.

Lemma eq_of_extens : forall l1 l2,
  length l1 = length l2 ->
  (forall i, index l1 i -> l1[i] = l2[i]) ->
  l1 = l2.
Proof using. intros. applys~ eq_of_extens_range. Qed.

End Read.

Global Opaque read_inst.


(* ---------------------------------------------------------------------- *)
(** * [update], with index as [int], as typeclass *)

Definition update_impl A (l:list A) (i:int) (v:A) : list A :=
  If i < 0 then l else LibList.update (abs i) v l.

Instance update_inst : forall A, BagUpdate int A (list A).
Proof using. constructor. rapply (@update_impl A). Defined.

Section Update.
Transparent index_inst read_inst update_inst.
Context (A : Type) `{IA:Inhab A}.
Implicit Types x v w : A.
Implicit Types l : list A.
Implicit Types i j : int.

Lemma length_update : forall l i v,
  length (l[i:=v]) = length l.
Proof using.
  intros. unfold update_inst, update_impl, length, update. simpl.
  case_if. math. rewrite~ length_update.
Qed.

Lemma index_update_eq : forall l i j v,
  index (l[j:=v]) i = index l i.
Proof using. intros. rewrite index_eq_index_length in *. rewrite~ length_update. Qed.

Lemma index_update : forall l i j v,
  index l i -> 
  index (l[j:=v]) i.
Proof using. intros. rewrite~ index_update_eq. Qed.

Lemma read_update_case : forall l i j v,
  index l j ->
  l[i:=v][j] = (If i = j then v else l[j]).
Proof using.
  introv. unfold index_inst, index_impl, update_inst, update_impl, update,
    read_inst, read_impl. simpl. introv N. rewrite int_index_eq in N.
  case_if. math.
  case_if. case_if. auto. case_if.
    subst. rewrite~ nth_update_same. apply lt_nat_of_lt_int. rewrite abs_nonneg; try math.
    rewrite~ nth_update_neq. apply neq_nat_of_neq_int. rewrite abs_nonneg; try math.
     rewrite abs_nonneg; try math.
Qed.

Lemma read_update_same : forall l i v,
  index l i -> 
  (l[i:=v])[i] = v.
Proof using. introv N. rewrite~ read_update_case. case_if~. Qed.

Lemma read_update_neq : forall l i j v,
  index l j ->
  (i <> j) -> 
  (l[i:=v])[j] = l[j].
Proof using. introv N. rewrite~ read_update_case. case_if; auto_false~. Qed.

End Update.

Section UpdateNoInhab.
Transparent index_inst read_inst update_inst.
Context (A : Type).
Implicit Types x v w : A.
Implicit Types l : list A.
Implicit Types i j : int.

Lemma update_zero : forall v x l,
  (x::l)[0:=v] = v::l.
Proof using. 
  intros. unfold update, update_inst, update_impl.
  case_if. false; math. rewrite~ update_zero.
Qed.

Lemma update_cons_pos : forall n v x l,
  n > 0 ->
  (x::l)[n:=v] = x::(l[(n-1):=v]).
Proof using. 
  introv N. unfold update, update_inst, update_impl.
  do 2 (case_if; try solve [ false; math ]).
  rewrite~ update_cons_pos. 
  { fequals_rec. rewrite <- abs_gt_minus_nat. fequals. math. }
  { applys gt_nat_of_gt_int. rewrite abs_nonneg; math. }
Qed.

Lemma update_update_same : forall l i v w,
  index l i ->
  l[i:=v][i:=w] = l[i:=w].
Proof using. 
  intros. asserts IA: (Inhab A). typeclass.
  eapply eq_of_extens; repeat rewrite length_update. { auto. }
  intros k Hk. repeat rewrite index_update_eq in Hk.
  repeat rewrite read_update_case by eauto using index_update.
  case_if~.
Qed.

Lemma update_update_neq : forall l i j v w,
  index l i -> 
  index l j -> 
  i <> j -> 
  l[i:=v][j:=w] = l[j:=w][i:=v].
Proof using.
  intros. asserts IA: (Inhab A). typeclass.
  applys eq_of_extens; repeat rewrite length_update. { auto. }
  intros k Hk. repeat rewrite index_update_eq in Hk.
  repeat rewrite read_update_case by eauto using index_update.
  repeat case_if~.
Qed.

Lemma update_app_l : forall l1 i l2 v,
  0 <= i < length l1 ->
  (l1 ++ l2)[i:=v] = (l1[i:=v]) ++ l2.
Proof using.
  introv N. asserts IA: (Inhab A). typeclass.
  unfold LibContainer.update, update_inst, update_impl.
  rewrite length_eq in N. case_if~. rewrite~ update_app_l. 
  applys lt_nat_of_lt_int. rewrite~ abs_nonneg. 
Qed.

Lemma update_app_r : forall l2 j l1 i ij v,
  i = length l1 ->
  0 <= j ->
  ij = i + j ->
  (l1 ++ l2)[ij:=v] = l1 ++ (l2[j:=v]).
Proof using.
  intros. asserts IA: (Inhab A). typeclass. subst ij.
  unfold LibContainer.update, update_inst, update_impl.
  do 2 (case_if; [ math | ]).
  rewrite Zabs2Nat.inj_add; try math. subst i.
  rewrite length_eq. rewrite abs_nat.
  rewrite~ update_app_r. fequals_rec. math.
Qed.

Lemma update_middle : forall i l1 l2 v w,
  i = length l1 ->
  (l1 ++ w :: l2)[i := v] = l1 & v ++ l2.
Proof using. 
  introv E. rewrites~ (>> update_app_r 0 i).
  rewrite update_zero. rew_list~.
Qed.

End UpdateNoInhab.

Global Opaque update_inst.



(* ---------------------------------------------------------------------- *)
(** * [make], with length as [int] *)

Definition make A (n:int) (v:A) : list A :=
  If n < 0 then arbitrary else make (abs n) v.

Section Make.
Transparent index_inst read_inst.
Context (A : Type) {IA:Inhab A}.
Implicit Types x v : A.
Implicit Types l : list A.
Implicit Types n i : int.

Lemma length_make : forall n v,
  n >= 0 ->
  length (make n v) = n.
Proof using.
  introv N. unfold make. case_if. math.
  unfold length. rewrite LibList.length_make.
  rewrite~ abs_nonneg.
Qed.

Lemma index_make : forall n i v,
  index n i ->
  index (make n v) i.
Proof using.
  introv H. rewrite index_eq_index_length.
  rewrite int_index_eq in H.
  rewrite~ length_make.
Qed.

Lemma read_make : forall i n v,
  index n i -> 
  (make n v)[i] = v.
Proof using.
  introv N. rewrite int_index_eq in N. 
  unfold make, read_inst, read_impl, nth.
  case_if. math. simpl. case_if. math.
  applys nth_make. forwards: lt_abs_abs i n; try math.
Qed.

Lemma make_zero : forall v, 
  make 0 v = nil.
Proof using.
  intros. unfold make. case_if. { false; math. }
  asserts_rewrite (abs 0 = 0%nat). 
  { applys eq_nat_of_eq_int. rewrite abs_nonneg; math. }
  auto.
Qed.

End Make.

Section MakeNoInhab.
Transparent index_inst read_inst.
Context (A : Type).
Implicit Types x v : A.
Implicit Types l : list A.
Implicit Types n i : int.

Lemma make_succ_l : forall n v, 
  n >= 0 -> 
  make (n+1) v = v :: make n v.
Proof using.
  introv N. unfold make. case_if; case_if; try solve [false;math].
  rewrite <- LibList.make_succ. fequal.
  { rewrite succ_abs_eq_abs_one_plus. fequal. math. math. }
Qed.

Lemma make_succ_r : forall n v, 
  n >= 0 -> 
  make (n+1) v = make n v & v.
Proof using.
  intros. asserts IA: (Inhab A). applys Inhab_of_val v.
  applys eq_of_extens_range.
  { rewrite length_make. rew_list. rewrite length_make.
    math. math. math. }
  { intros i Ei. rewrite length_make in Ei; [| math ].
    rewrite read_make; [| rewrite int_index_eq; math ].
    rewrite read_app. rewrite length_make; [|math].
    case_if as C.
    { rewrite read_make. auto. rewrite int_index_eq; math. }
    { math_rewrite (i-n = 0). rewrite~ read_zero. } }
Qed.

Lemma make_eq_cons_make_pred : forall n v,
  0 < n -> 
  make n v = v :: (make (n-1) v).
Proof using.
  intros. math_rewrite (n = (n-1)+1). rewrite make_succ_l.
  fequals_rec. math. math.
Qed.

End MakeNoInhab.

Global Opaque make.


(* ---------------------------------------------------------------------- *)
(** * [LibList.map] interactions with [LibListZ] operations *)

Section Map.
Transparent index_inst read_inst update_inst.
Context (A : Type).
Implicit Types x v : A.
Implicit Types l : list A.
Implicit Types n i : int.

Lemma length_map : forall A B (l:list A) (f:A->B),
  length (map f l) = length l.
Proof using. intros. unfold length. rewrite~ length_map. Qed.

Lemma index_map_eq : forall A B (l:list A) i (f:A->B),
  index (map f l) i = index l i.
Proof using. intros. rewrite index_eq_inbound in *. rewrite~ length_map. Qed.

Lemma index_map : forall A B (l:list A) i (f:A->B),
  index l i -> index (map f l) i.
Proof using. intros. rewrite~ index_map_eq. Qed.

Lemma map_update : forall A B (l:list A) (i:int) (x:A) (f:A->B),
  index l i ->
  map f (l[i := x]) = (map f l)[i := f x].
Proof using.
  introv H. rewrite index_eq_inbound in H.
  unfold update_inst, update_impl, update. simpl.
  case_if. { false; math. }
  { applys LibList.map_update. 
    { applys lt_nat_of_lt_int. rewrite abs_nonneg; math. } }
Qed.

Lemma read_map : forall `{IA:Inhab A} `{IB:Inhab B} (l:list A) (i:int) (f:A->B),
  index l i ->
  (map f l)[i] = f (l[i]).
Proof using.
  introv H. rewrite index_eq_inbound in H.
  unfold read_inst, read_impl. simpl. case_if.
  { false; math. }
  { rewrite nth_map. auto.
    applys lt_nat_of_lt_int. rewrite abs_nonneg; math. }
Qed.

End Map.


(* ---------------------------------------------------------------------- *)
(** * [card], with result as [nat], as typeclass *)

(** Note that [card] produces a [nat], whereas [length] produces an [int]. 
    Currently, in practice, we use [LibList.length] rather than [card]. *)

Definition card_impl A (l:list A) : nat :=
  LibList.length l.

Instance card_inst : forall A, BagCard (list A).
Proof using. constructor. rapply (@card_impl A). Defined.

Global Opaque card_inst.


(* ---------------------------------------------------------------------- *)
(** * Normalization tactics *)

(** [rew_array_nocase] is a light normalization tactic for array *)

Hint Rewrite @read_make @length_make @length_update @read_update_same
  : rew_array_nocase.

Tactic Notation "rew_array_nocase" :=
  autorewrite with rew_array_nocase.
Tactic Notation "rew_array_nocase" "in" hyp(H) :=
  autorewrite with rew_array_nocase in H.
Tactic Notation "rew_array_nocase" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_array_nocase).
  (* autorewrite with rew_array_nocase in *. *)
Tactic Notation "rew_array_nocase" "~" :=
  rew_array_nocase; auto_tilde.
Tactic Notation "rew_array_nocase" "*" :=
  rew_array_nocase; auto_star.
Tactic Notation "rew_array_nocase" "~" "in" hyp(H) :=
  rew_array_nocase in H; auto_tilde.
Tactic Notation "rew_array_nocase" "*" "in" hyp(H) :=
  rew_array_nocase in H; auto_star.
Tactic Notation "rew_array_nocase" "~" "in" "*" :=
  rew_array_nocase in *; auto_tilde.
Tactic Notation "rew_array_nocase" "*" "in" "*" :=
  rew_array_nocase in *; auto_star.

(** [rew_array] is a normalization tactic for array, which introduces
    case analyses for all read-on-update operations. *)

Hint Rewrite @read_make @length_make @length_update @read_update_same
  @read_update_case @read_cons_case @read_last_case : rew_array.

Tactic Notation "rew_array" :=
  autorewrite with rew_array.
Tactic Notation "rew_array" "in" hyp(H) :=
  autorewrite with rew_array in H.
Tactic Notation "rew_array" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_array).
  (* autorewrite with rew_array in *. *)
Tactic Notation "rew_array" "~" :=
  rew_array; auto_tilde.
Tactic Notation "rew_array" "*" :=
  rew_array; auto_star.
Tactic Notation "rew_array" "~" "in" hyp(H) :=
  rew_array in H; auto_tilde.
Tactic Notation "rew_array" "*" "in" hyp(H) :=
  rew_array in H; auto_star.
Tactic Notation "rew_array" "~" "in" "*" :=
  rew_array in *; auto_tilde.
Tactic Notation "rew_array" "*" "in" "*" :=
  rew_array in *; auto_star.



(* ********************************************************************** *)
(** Restore automation *)

Ltac auto_tilde ::= auto_tilde_default.




(* ********************************************************************** *)
(** FUTURE WORK *)

(*-- Lemmas on tail; is this useful? *)

(*
Lemma length_tail : forall l,
  l <> nil -> 
  length (tail l) = length l - 1.
Proof using. induction l; intros; simpl; unfold length; rew_list. congruence. math. Qed.

Lemma length_tail_le : forall l,
  length (tail l) <= length l.
Proof using. destruct l; simpl; unfold length; rew_list; math. Qed.

Lemma length_le_1_inv_tail_eq_nil : forall l,
  length l <= 1 -> 
  tail l = nil.
Proof using.
  intros. destruct l; eauto.
  simpl. unfold length in *. rew_list in *.
  eapply length_zero_inv. math.
Qed.
*)


(* ---------------------------------------------------------------------- *)
(** * [binds], with length as [int], as typeclass *)

(* --LATER: is this any useful?

  Definition binds_impl A (l:list A) (i:int) (v:A) : Prop :=
    index_impl l i /\ nth i l = v.

  Instance binds_inst : forall A, BagBinds int A (list A).
  Proof using. constructor. rapply (@binds_impl A). Defined.

  Global Opaque binds_inst

*)

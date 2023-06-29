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

Open Scope Int_scope.
Local Open Scope comp_scope.

Ltac auto_tilde ::= eauto with maths.


(* ********************************************************************** *)
(** * Tactics *)


(* ---------------------------------------------------------------------- *)
(** ** [rew_listp] for operations with preconditions *)

Tactic Notation "rew_listp" :=
  autorewrite with rew_listp.
Tactic Notation "rew_listp" "~" :=
  rew_listp; auto_tilde.
Tactic Notation "rew_listp" "*" :=
  rew_listp; auto_star.
Tactic Notation "rew_listp" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_listp).
  (* autorewrite with rew_list in *. *)
Tactic Notation "rew_listp" "~" "in" "*" :=
  rew_listp in *; auto_tilde.
Tactic Notation "rew_listp" "*" "in" "*" :=
  rew_listp in *; auto_star.
Tactic Notation "rew_listp" "in" hyp(H) :=
  autorewrite with rew_listp in H.
Tactic Notation "rew_listp" "~" "in" hyp(H) :=
  rew_listp in H; auto_tilde.
Tactic Notation "rew_listp" "*" "in" hyp(H) :=
  rew_listp in H; auto_star.

(* ---------------------------------------------------------------------- *)
(** ** [rew_index] for operations on indices *)

Tactic Notation "rew_index" :=
  autorewrite with rew_index.
Tactic Notation "rew_index" "in" hyp(H) :=
  autorewrite with rew_index in H.
Tactic Notation "rew_index" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_index).
(* autorewrite with rew_index in *. *)
Tactic Notation "rew_index" "~" :=
  rew_index; auto_tilde.
Tactic Notation "rew_index" "*" :=
  rew_index; auto_star.
Tactic Notation "rew_index" "~" "in" hyp(H) :=
  rew_index in H; auto_tilde.
Tactic Notation "rew_index" "*" "in" hyp(H) :=
  rew_index in H; auto_star.
Tactic Notation "rew_index" "~" "in" "*" :=
  rew_index in *; auto_tilde.
Tactic Notation "rew_index" "*" "in" "*" :=
  rew_index in *; auto_star.

(* ---------------------------------------------------------------------- *)
(** ** [rew_array] for case-analysis free rewriting *)

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

(* ---------------------------------------------------------------------- *)
(** ** [rew_array] for case-analysis aware rewriting *)

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

#[global] Hint Rewrite int_index_eq : rew_array.


(* ---------------------------------------------------------------------- *)
(** ** [index_prove] for automating proofs on indices *)

Ltac index_prove tt :=
  rew_index; repeat case_if; rew_list in *; math.

(* Use [Import IndexHints] for loading hints *)

Module IndexHints.
  #[global]
  Hint Extern 1 (index _ _) => index_prove tt.
End IndexHints.


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

End Length.

(* other inversion lemmas *)

Lemma Forall2_inv_length : forall A B (P:A->B->Prop) r s,
  Forall2 P r s ->
  length r = length s.
Proof using. introv E. unfold length. lets*: Forall2_inv_length E. Qed.

#[global] Hint Rewrite length_nil length_cons length_app
 length_last : rew_list.
#[global] Hint Rewrite length_nil length_cons length_app
 length_last : rew_listx.
 (* --TODO: should we use a separate [rew_listZ] data base? probably so *)

(** Automation for [math], to unfold [length] *)

#[global] Hint Rewrite length_eq : rew_maths.
#[global] Hint Rewrite length_cons : rew_index.
#[global] Hint Rewrite length_app : rew_index.

(** Demo of automation with maths *)

Goal forall A (l : list A), 0 <= length l.
Proof using. intros. math. Qed.

Goal forall (l : list Z) (s n : int),
  s <= n ->
  s = length l ->
  n >= 0.
Proof using. intros. math. Qed.


(* ---------------------------------------------------------------------- *)
(** * Inversion lemmas for structural composition *)

Section AppInversion.
Variables A : Type.
Implicit Types x : A.
Implicit Types l : list A.

(**------- Length -------- *)

Lemma length_zero_inv : forall l,
  length l = 0 ->
  l = nil.
Proof using. intros. unfolds length. applys~ LibList.length_zero_inv. Qed.

Lemma length_zero_eq_eq_nil : forall l,
  (length l = 0) = (l = nil).
Proof using.
  intros. unfolds length. rewrite <-LibList.length_zero_eq_eq_nil. math.
Qed.

Lemma length_neq_inv : forall l1 l2,
  length l1 <> length l2 ->
  (l1 <> l2).
Proof using. introv N E. subst*. Qed.

Lemma length_pos_inv_cons : forall l,
  (length l > 0) ->
  exists x l', l = x :: l'.
Proof using.
  intros. unfolds length. applys~ LibList.length_pos_inv_cons.
Qed.

Lemma length_pos_inv_last : forall l,
  (length l > 0) ->
  exists x l', l = l' & x.
Proof using.
  intros. unfolds length. applys~ LibList.length_pos_inv_last.
Qed.

End AppInversion.

(* ---------------------------------------------------------------------- *)
(** * [index], with length as [int], as typeclass *)

Definition index_impl A (l:list A) (i:int) : Prop :=
  index (LibList.length l : int) i.

#[global]
Instance index_inst : forall A, BagIndex int (list A).
Proof using. constructor. rapply (@index_impl A). Defined.

Global Opaque index_inst.

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

Hint Rewrite index_eq_index_length int_index_eq : rew_index.

Lemma index_app_l : forall l l' i,
  index l i ->
  index (l++l') i.
Proof using. introv. rew_index. math. Qed.

Lemma index_app_r : forall l l' i,
  index l' (i - length l) ->
  i >= length l ->
  index (l++l') i.
Proof using. introv. rew_index. math. Qed.

Lemma index_app_eq : forall l l' i,
  index (l++l') i = (If i < length l then index l i else index l' (i - length l)).
Proof using. intros. extens. rew_index. iff; case_if; math. Qed.

(** Reformulation of above, helpful for automation *)

Lemma index_of_index_length' : forall l n i,
  index n i ->
  n = length l ->
  index l i.
Proof using. intros. subst. rewrite~ index_eq_index_length. Qed.

End Index.

#[global] Hint Rewrite index_eq_index_length int_index_eq index_app_eq : rew_index.


(* ---------------------------------------------------------------------- *)
(** * [read], with length as [int], as typeclass *)

Definition read_impl `{Inhab A} (l:list A) (i:int) : A :=
  If i < 0 then arbitrary else nth (abs i) l.

#[global]
Instance read_inst : forall `{Inhab A}, BagRead int A (list A).
Proof using. constructor. rapply (@read_impl A H). Defined.

Section Read.
Context (A : Type) (IA:Inhab A).
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types n i : int.

Lemma read_cons_case : forall l i v,
  (v::l)[i] = (If i = 0 then v else l[i-1]).
Proof using IA.
  introv. simpl. unfold read_impl. case_if.
  { case_if. math. case_if~. math. }
  { case_if~.
    { subst. rewrite abs_0. rew_listx~. }
    { rewrite~ abs_eq_succ_abs_minus_one. rew_listx.
      case_if. math. auto. } }
Qed.

Lemma read_cons_pos : forall x l i,
  i > 0 ->
  (x::l)[i] = l[i-1].
Proof using IA. introv P. rewrite read_cons_case. case_if; try math. auto. Qed.

Lemma read_zero : forall x l,
  (x::l)[0] = x.
Proof using IA.
  intros. rewrite read_cons_case. case_if. auto.
Qed.

Lemma read_succ : forall x l i,
  0 <= i < length l ->
  (x::l)[i+1] = l[i].
Proof using IA.
  introv M. rewrite read_cons_case. case_if. { math. }
  fequals. math.
Qed.

Lemma read_last_case : forall l i v,
  (l & v)[i] = (If i = length l then v else l[i]).
Proof using IA.
  introv. simpl. unfold read_impl. case_if.
  { case_if~; math. }
  { rewrite nth_last_case. rewrite~ abs_eq_nat_eq. }
Qed.

Lemma read_middle : forall i l1 l2 x,
  i = length l1 ->
  (l1 ++ x :: l2)[i] = x.
Proof using IA.
  introv M. rewrite length_eq in M. unfold read, read_inst, read_impl.
  case_if. { false; math. }
  rewrite~ nth_middle.
Qed.

Lemma read_app : forall i l1 l2,
  (l1 ++ l2)[i] = (If i < length l1 then l1[i] else l2[i - length l1]).
Proof using IA.
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
Proof using IA.
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
Proof using IA. intros. applys~ eq_of_extens_range. Qed.

(** [mem] *)

Lemma mem_read : forall l i,
  index l i ->
  mem l[i] l.
Proof using IA.
  intros l. induction l; introv Hi.
  { rew_index in Hi. rew_list* in Hi. math. }
  { rewrite read_cons_case. case_if*. applys mem_cons_r.
    applys IHl. rew_index in *. math. }
Qed.

End Read.

Lemma mem_inv_read : forall A (IA:Inhab A) (l:list A) x,
  mem x l ->
  exists i, index l i /\ x = l[i].
Proof using.
  intros. gen x. induction l; introv Hx; inversion Hx; subst.
  { exists 0. (* list_cases *) splits*. rewrite* read_zero. }
  { lets* (i,(Hi&->)): (IHl x). (* list_cases *)
    rew_index in *. exists (i+1). split*. rewrite* read_succ. }
Qed.

Lemma Forall2_inv_read : forall A (IA:Inhab A) B (IB:Inhab B) P (xs:list A) (ys:list B) i,
  Forall2 P xs ys ->
  index xs i ->
  P xs[i] ys[i].
Proof using.
  induction xs; introv HF Hi; rew_index in Hi; rew_list in Hi.
  { math. }
  { lets (x&xs'&M1&M2&M3) : Forall2_cons_l_inv HF. (* list_cases *)
    subst. do 2 rewrite read_cons_case. case_if. { auto. } { applys* IHxs. } }
Qed.

Global Opaque read_inst.

#[global] Hint Rewrite read_zero : rew_list.
#[global] Hint Rewrite read_zero : rew_listx.


(* ---------------------------------------------------------------------- *)
(** * [update], with index as [int], as typeclass *)

Definition update_impl A (l:list A) (i:int) (v:A) : list A :=
  If i < 0 then l else LibList.update (abs i) v l.

#[global]
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
    subst. rewrite~ nth_update_same.
    rewrite~ nth_update_neq.
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
Qed.

Lemma update_cons_case : forall x l i z,
  index (x::l) i ->
  (x::l)[i:=z] = If i = 0 then z::l else x::(l[i-1:=z]).
Proof using.
  introv H. case_if.
  { subst. rewrite* update_zero. }
  { rewrite* update_cons_pos. rew_index in H. math. }
Qed.

Lemma update_same : forall (IA:Inhab A) l i,
  index l i ->
  l[i:=l[i]] = l.
Proof using.
  intros IA l. induction l; intros i Hi.
  { rew_index in Hi. rew_list in Hi. false. math. }
  { rew_index in *. rewrite* update_cons_case. case_if.
    { fequals. (* list_cases*. *) subst. rewrite* read_zero. }
    { fequals. rewrite* read_cons_pos. math. } }
Qed.

Lemma update_update_same : forall l i v w,
  index l i ->
  l[i:=v][i:=w] = l[i:=w].
Proof using.
  intros. asserts IA2: (Inhab A). typeclass.
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

Lemma Forall_update : forall P l i x,
  Forall P l ->
  P x ->
  index l i ->
  Forall P (l[i:=x]).
Proof using.
  introv. gen i. induction l; introv HL Hx Hi; rew_listx.
  { (* --TODO: lemma *) rew_index in Hi. rew_list in *. false. math. }
  { rew_index in *. rew_listx* in HL. destruct HL.
    rewrite* update_cons_case. case_if*; rew_listx*. }
Qed.

End UpdateNoInhab.

#[global] Hint Rewrite update_same length_update : rew_listx.
#[global] Hint Rewrite index_update_eq : rew_array.
#[global] Hint Rewrite index_update_eq : rew_index.

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

Lemma index_make_eq : forall n i v,
  n >= 0 ->
  index (make n v) i = index n i.
Proof using.
  intros. rewrite index_eq_index_length.
  rewrite* length_make.
Qed.

Lemma read_make : forall i n v,
  index n i ->
  (make n v)[i] = v.
Proof using.
  introv N. rewrite int_index_eq in N.
  unfold make, read_inst, read_impl.
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

#[global] Hint Rewrite length_make read_make : rew_listp.
#[global] Hint Rewrite index_make_eq : rew_array.
#[global] Hint Rewrite length_make index_make_eq : rew_index.

Global Opaque make.


(* ---------------------------------------------------------------------- *)
(** * [LibList.rev] interactions with [LibListZ] operations *)

Section Rev.
Variables (A : Type).
Implicit Types x : A.
Implicit Types l : list A.

Lemma length_rev : forall l,
  length (rev l) = length l.
Proof using. intros. unfold length. rew_list~. Qed.

Lemma index_rev_eq : forall l i,
  index (rev l) i = index l i.
Proof using.
  extens. intros.
  now rewrite index_eq_index_length, length_rev, index_eq_index_length.
Qed.

End Rev.

#[global] Hint Rewrite length_rev : rew_list.
#[global] Hint Rewrite length_rev : rew_listx.
#[global] Hint Rewrite index_rev_eq : rew_index.

(* ---------------------------------------------------------------------- *)
(** * [LibList.map]: [map] interactions with [LibListZ] operations *)

Section Map.
Transparent index_inst read_inst update_inst.
(*Context (A : Type).
Implicit Types x v : A.
Implicit Types l : list A.
*)
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

Lemma map_make : forall A B (f:A->B) (n:int) (v:A),
  n >= 0 ->
  map f (make n v) = make n (f v).
Proof using.
  Transparent make.
  intros. unfold make. case_if. { false; math. }
  applys map_make.
Qed.

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

#[global] Hint Rewrite length_map index_map_eq : rew_listx.
#[global] Hint Rewrite length_map index_map_eq : rew_index.


(* ---------------------------------------------------------------------- *)
(** * [LibList.filter] interactions with [LibListZ] operations *)

Section Filter.
Variables (A : Type).
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types P : A -> Prop.

Lemma length_filter : forall l P,
  length (filter P l) <= length l.
Proof using.
  intros. unfolds length. forwards~: LibList.length_filter l P.
Qed.

Lemma filter_length_two_disjoint : forall (P Q : A-> Prop) l,
  (forall x, mem x l -> P x -> Q x -> False) ->
  length (filter P l) + length (filter Q l) <= length l.
Proof using.
  intros. unfolds length.
  forwards~: LibList.filter_length_two_disjoint.
Qed.

Lemma filter_length_partition : forall P l,
    length (filter (fun x => P x) l)
  + length (filter (fun x => ~ P x) l)
  <= length l.
Proof using.
  intros. unfolds length. forwards~: LibList.filter_length_partition P l.
Qed.

Lemma length_filter_eq_mem_ge_one : forall x l,
  mem x l ->
  length (filter (= x) l) >= 1.
Proof using.
  intros. unfolds length. forwards~: LibList.length_filter_eq_mem_ge_one.
Qed.

End Filter.

(* ---------------------------------------------------------------------- *)
(** * [LibList.remove] interactions with [LibListZ] operations *)

Section Remove.
Variables (A : Type).
Implicit Types a x : A.
Implicit Types l : list A.

Lemma length_remove : forall l a,
  length (LibList.remove a l) <= length l.
Proof using. intros. rewrite remove_as_filter. applys length_filter. Qed.

Lemma length_remove_mem : forall x l,
  mem x l ->
  length (LibList.remove x l) < length l.
Proof using.
  intros. unfolds length. forwards~: LibList.length_remove_mem.
Qed.

End Remove.

(* ---------------------------------------------------------------------- *)
(** ** Take, with an [int] as the number of elements *)

Definition take A (n:int) (l:list A) : list A :=
  LibList.take (to_nat n) l.

Section Take.
Variables (A : Type).
Implicit Types n : int.
Implicit Types x : A.
Implicit Types l : list A.

Lemma take_nil : forall n,
  take n (@nil A) = nil.
Proof using. intros. unfold take. apply LibList.take_nil. Qed.

Lemma take_zero : forall l,
  take 0 l = nil.
Proof using. auto. Qed.

Lemma take_succ : forall x l n,
  0 <= n ->
  take (n+1) (x::l) = x :: (take n l).
Proof using.
  intros. unfold take. rew_to_nat_nonneg~.
  rewrite Nat.add_1_r. apply LibList.take_succ.
Qed.

Definition take_cons := take_succ.

Lemma take_cons_pos : forall x l n,
  (n > 0) ->
  take n (x::l) = x :: (take (n-1) l).
Proof using.
  intros. unfold take. rew_to_nat_nonneg~.
  rewrite~ LibList.take_cons_pos.
Qed.

Lemma take_cons_case : forall x l n,
  n >= 0 ->
  take n (x::l) = If n = 0 then nil else x :: (take (n-1) l).
Proof using.
  introv Hn. case_if.
  { subst. applys take_zero. }
  { applys* take_cons_pos. math. }
Qed.

Lemma take_pos_last : forall (IA:Inhab A) l i,
  index l (i-1) ->
  take i l = take (i-1) l & l[i-1].
Proof using. 
  introv Hi. gen i. induction l; intros; rew_index in Hi; rew_list in Hi.
  { math. }
  { rewrite take_cons_pos; try math.
    rewrite take_cons_case; try math. case_if as C.
    { rew_list. rewrite C. rewrite take_zero. rewrite* read_zero. }
    { rew_list. fequals. rewrite IHl; [|rew_index;math].
       fequals. rewrite* read_cons_pos. math. } }
Qed.

Lemma take_neg : forall n l,
  n <= 0 ->
  take n l = nil.
Proof using. intros. unfold take. rewrite~ to_nat_neg. Qed.

Lemma take_ge : forall n l,
  (n >= length l) ->
  take n l = l.
Proof using.
  intros. unfold take, length in *. applys~ LibList.take_ge.
Qed.

Lemma take_is_prefix : forall n l,
  exists q, l = take n l ++ q.
Proof using.
  intros. unfold take. applys~ LibList.take_is_prefix.
Qed.

Lemma take_app_l : forall n l l',
  (n <= length l) ->
  take n (l ++ l') = take n l.
Proof using.
  intros. tests: (0 <= n).
  { unfold take, length in *.
    applys~ LibList.take_app_l. }
  { rewrite !take_neg; auto; math. }
Qed.

Lemma take_app_r : forall n l l',
  (n >= length l) ->
  take n (l ++ l') = l ++ take (n - length l) l'.
Proof using.
  intros. unfold take, length in *. rew_to_nat_nonneg~.
  applys~ LibList.take_app_r.
Qed.

Lemma take_prefix_length : forall l l',
  take (length l) (l ++ l') = l.
Proof using.
  intros. unfold take, length. rew_to_nat_nonneg~.
  applys~ LibList.take_prefix_length.
Qed.

Lemma take_full_length : forall l,
  take (length l) l = l.
Proof using.
  intros. unfold take, length. rew_to_nat_nonneg~.
  apply LibList.take_full_length.
Qed.

(* See below for [length_take] and other properties *)

End Take.

(* Arguments take [A] : simpl never. *)

#[global] Hint Rewrite take_nil take_zero take_succ : rew_listx.

(* Note: [take_prefix_length] and [take_full_length]
   may be safely added to [rew_listx]. *)

(* ---------------------------------------------------------------------- *)
(** ** Drop, with an [int] as the number of elements. *)

Definition drop A (n:int) (l:list A) : list A :=
  LibList.drop (to_nat n) l.

Section Drop.
Variables (A : Type).
Implicit Types n : int.
Implicit Types x : A.
Implicit Types l : list A.

Lemma drop_nil : forall n,
  drop n (@nil A) = nil.
Proof using. intros. unfold drop. apply LibList.drop_nil. Qed.

Lemma drop_zero : forall l,
  drop 0 l = l.
Proof using. auto. Qed.

Lemma drop_succ : forall x l n,
  0 <= n ->
  drop (n+1) (x::l) = (drop n l).
Proof using.
  intros. unfold drop. rew_to_nat_nonneg~.
  rewrite Nat.add_1_r. apply LibList.drop_succ.
Qed.

Definition drop_cons := drop_succ.

Lemma drop_neg : forall n l,
  n <= 0 ->
  drop n l = l.
Proof using. intros. unfold drop. rewrite~ to_nat_neg. Qed.

Lemma drop_cons_pos : forall x l n,
  (n > 0) ->
  drop n (x::l) = drop (n-1) l.
Proof using.
  intros. unfold drop. rew_to_nat_nonneg~.
  apply~ LibList.drop_cons_pos.
Qed.

Lemma drop_is_suffix : forall n l,
  exists q, l = q ++ drop n l.
Proof using.
  intros. unfold drop. apply LibList.drop_is_suffix.
Qed.

Lemma drop_app_l : forall n l l',
  (n <= length l) ->
  drop n (l ++ l') = drop n l ++ l'.
Proof using.
  intros. tests: (0 <= n).
  { unfold drop, length in *.
    apply LibList.drop_app_l. rewrites~ to_nat_le_nat_le. }
  { rewrite !drop_neg; auto; math. }
Qed.

Lemma drop_app_r : forall n l l',
  (n >= length l) ->
  drop n (l ++ l') = drop (n - length l) l'.
Proof using.
  intros. unfold drop, length in *. rew_to_nat_nonneg~.
  apply LibList.drop_app_r. rewrites~ to_nat_ge_nat_ge.
Qed.

Lemma drop_app_length : forall l l',
  drop (length l) (l ++ l') = l'.
Proof using.
  intros. unfold drop, length. rew_to_nat_nonneg~.
  apply LibList.drop_app_length.
Qed.

Lemma drop_at_length : forall l,
  drop (length l) l = nil.
Proof using.
  intros. unfold drop, length. rew_to_nat_nonneg~.
  apply LibList.drop_at_length.
Qed.

Lemma drop_drop : forall l n m,
  n >= 0 ->
  m >= 0 ->
  drop n (drop m l) = drop (n+m) l.
Proof using.
  introv Hn Hm.
  rewrite* <- (to_nat_nonneg Hn).
  rewrite* <- (to_nat_nonneg Hm).
  unfold drop.
  applys_eq LibList.drop_drop. fequals. math.
Qed.

(* See below for [length_drop] and other properties *)

End Drop.

(* Arguments drop [A] : simpl never. *)

#[global] Hint Rewrite drop_at_length drop_nil drop_zero drop_succ : rew_listx.
#[global] Hint Rewrite drop_drop : rew_listp.

#[global] Hint Rewrite drop_nil drop_zero drop_succ : rew_listx.
(* Note: [drop_prefix_length] and [drop_full_length]
   may be safely added to [rew_list]. *)

(* ---------------------------------------------------------------------- *)
(** ** Take and drop decomposition of a list *)

Section TakeAndDrop.
Variables (A : Type).
Implicit Types x : A.
Implicit Types l : list A.

Lemma take_app_drop_spec : forall n l f r,
  f = take n l ->
  r = drop n l ->
  (0 <= n <= length l ->
      l = f ++ r
   /\ length f = n
   /\ length r = length l - n) /\
  (n <= 0 ->
    f = nil /\ r = l).
Proof using.
  introv ? ?. split.
  { intros (? & Hn). unfold take, drop, length in *.
    forwards~ (? & ? & Hlenrest): @LibList.take_app_drop_spec (to_nat n) l f r. }
  { intros. rewrites~ take_neg in *. rewrites~ drop_neg in *. }
Qed.

Lemma take_spec : forall n l,
  0 <= n <= length l ->
  exists l', length (take n l) = n
          /\ l = (take n l) ++ l'.
Proof using. introv E. forwards* (E1&_): take_app_drop_spec. forwards*: E1. Qed.

Lemma length_take_nonneg : forall n l,
  0 <= n <= length l ->
  length (take n l) = n.
Proof using. introv E. forwards~ (l'&N&M): take_spec n l. Qed.

Lemma length_take : forall n l,
  n <= length l ->
  length (take n l) = Z.max 0 n.
Proof using.
  intros. tests: (0 <= n).
  { rewrite~ length_take_nonneg. }
  { rewrite~ take_neg. rewrite~ Z.max_l. }
Qed.

Lemma read_take : forall (IA:Inhab A) l s i,
  s <= length l ->
  index s i ->
  (take s l)[i] = l[i].
Proof using. (* Note: could be proved without take_spec *)
  introv Hs Hi. rew_index in *.
  lets (l'&Hl&Hl'): take_spec s l. { math. }
  rewrite Hl' at 2. rewrite read_app. case_if*.
  { false. rewrite length_take_nonneg in C; try math. }
Qed.

Lemma drop_spec : forall n l,
  0 <= n <= length l ->
  exists l', length l' = n
          /\ l = l' ++ (drop n l).
Proof using. introv E. forwards* (E1&_): take_app_drop_spec. forwards*: E1. Qed.

Lemma read_drop : forall (IA:Inhab A) l (s i:int),
  0 <= s <= length l ->
  index (length l - s) i ->
  (drop s l)[i] = l[s+i].
Proof using.
  introv Hs Hi. rew_index in *.
  lets (l'&Hl&Hl'): drop_spec s l. { math. }
  rewrite Hl' at 2. rewrite read_app. case_if*.
  { false. math. } { fequals. math. }
Qed.

Lemma length_drop_nonneg : forall n l,
  0 <= n <= length l ->
  length (drop n l) = length l - n.
Proof using.
  introv E. forwards~ (l'&N&M): drop_spec n l.
  pattern l at 2. rewrite M. rew_list. math.
Qed.

Lemma length_drop : forall n l,
  n <= length l ->
  length (drop n l) = Z.min (length l) (length l - n).
Proof using.
  intros. tests: (0 <= n).
  { rewrite~ length_drop_nonneg. }
  { rewrite~ drop_neg. }
Qed.

Lemma list_eq_take_app_drop : forall n l,
  n <= length l ->
  take n l ++ drop n l = l.
Proof using.
  introv H. tests: (0 <= n).
  { forwards*: take_app_drop_spec n l. }
  { rewrite~ take_neg. rewrite~ drop_neg. }
Qed.

Lemma mem_drop_inv : forall l i x,
  mem x (drop i l) ->
  0 <= i <= length l ->
  mem x l.
Proof using.
  introv Hx Hi. rewrites* <- (>> list_eq_take_app_drop i).
  apply* mem_app_r.
Qed.

End TakeAndDrop.

Arguments take_app_drop_spec [A].
Arguments take_spec [A].
Arguments drop_spec [A].

#[global] Hint Rewrite read_take read_drop length_take length_drop : rew_listp.

(* ---------------------------------------------------------------------- *)
(** ** [sum], for lists of int values *)

Definition sum (l:list int) : int :=
  fold_right Z.add 0 l.

Lemma sum_nil :
  sum nil = 0.
Proof using. rew_listx*. Qed.

Lemma sum_cons : forall (l:list int) (x:int),
  sum (x::l) = x + sum l.
Proof using. rew_listx*. Qed.

#[global] Hint Rewrite sum_nil sum_cons : rew_listx.

Lemma sum_app : forall (l1 l2:list int),
  sum (l1 ++ l2) = sum l1 + sum l2.
Proof using. (* TOCLEAN: hints should come at the end of the section *)
  induction l1; intros l2; unfold sum; rew_listx*.
  rewrite* IHl1. unfold sum. math.
Qed.

#[global] Hint Rewrite sum_nil sum_cons sum_app : rew_listx.

(* Use of [sum] for [concat] *)

Lemma length_concat_eq_sum : forall A (l:list (list A)),
  length (concat l) = sum (map (length (A:=A)) l).
Proof using. intros. induction l; rew_listx; math. Qed.


(* ---------------------------------------------------------------------- *)
(** ** [count], returning an int *)

Definition count A (P: A -> Prop) (l: list A): int :=
  abs (LibList.count P l).

Section Count.
Variables A : Type.
Implicit Types l : list A.
Implicit Types P : A -> Prop.

Ltac gowith L :=
  let H := fresh in
  lets H: L;
  repeat (let x := fresh in intro x; specializes H x);
  unfold count in *; repeat rewrites~ abs_nonneg in *;
  try solve [
    first [ rewrites~ H in * | forwards~: H ];
    repeat case_if~
  ].

(* Rewriting *)

Lemma count_nil : forall P,
  count P nil = 0.
Proof using. auto. Qed.

Lemma count_one : forall P x,
  count P (x::nil) = If P x then 1 else 0.
Proof using. gowith LibList.count_one. Qed.

Lemma count_cons : forall P l x,
  count P (x::l) = count P l + If P x then 1 else 0.
Proof using. gowith LibList.count_cons. Qed.

Lemma count_app : forall P l1 l2,
  count P (l1++l2) = count P l1 + count P l2.
Proof using. gowith LibList.count_app. Qed.

Lemma count_last : forall P l x,
  count P (l&x) = count P l + If P x then 1 else 0.
Proof using. gowith LibList.count_last. Qed.

Lemma count_rev : forall P l,
  count P (rev l) = count P l.
Proof using. gowith LibList.count_rev. Qed.

Lemma count_eq_length_filter : forall P l,
  count P l = length (filter P l).
Proof using. gowith LibList.count_eq_length_filter. Qed.

(* Properties *)

Lemma count_nonneg : forall P l,
  0 <= count P l.
Proof using. intros. unfold count. math. Qed.

Lemma count_le_length : forall P l,
  count P l <= length l.
Proof using. gowith LibList.count_le_length. Qed.

(* Interactions with [Forall] *)

Lemma Forall_eq_count_eq_length : forall P l,
  Forall P l = (count P l = length l).
Proof using.
  intros. rewrite LibList.Forall_eq_count_eq_length, length_eq.
  unfold count. rewrite abs_nonneg; math.
Qed.

Lemma count_Forall : forall P l,
  Forall P l ->
  count P l = length l.
Proof using. introv. rewrite~ Forall_eq_count_eq_length. Qed.

Lemma Forall_of_count_eq_length : forall P l,
  count P l = length l ->
  Forall P l.
Proof using. introv. rewrite~ Forall_eq_count_eq_length. Qed.

(* Interactions with [Forall (pred_not P)] *)

Lemma Forall_not_eq_count_eq_zero : forall P l,
  Forall (fun x => ~ P x) l = (count P l = 0).
Proof using.
  intros. rewrite LibList.Forall_not_eq_count_eq_zero.
  unfold count. rewrite abs_nonneg; math.
Qed.

Lemma Forall_not_of_count_eq_zero : forall P l,
  count P l = 0 ->
  Forall (fun x => ~ P x) l.
Proof using. introv. rewrite~ Forall_not_eq_count_eq_zero. Qed.

Lemma count_eq_zero_of_Forall_not : forall P l,
  Forall (fun x => ~ P x) l ->
  count P l = 0.
Proof using. introv. rewrite~ Forall_not_eq_count_eq_zero. Qed.

(* Interactions with [Exists] *)

Lemma Exists_eq_count_pos : forall P l,
  Exists P l = (count P l > 0).
Proof using.
  intros. rewrite LibList.Exists_eq_count_pos.
  unfold count. rewrite abs_nonneg; math.
Qed.

Lemma Exists_of_count_pos : forall P l,
  count P l > 0 ->
  Exists P l.
Proof using. introv. rewrite~ Exists_eq_count_pos. Qed.

Lemma count_pos_of_Exists : forall P l,
  Exists P l ->
  count P l > 0.
Proof using. introv. rewrite~ Exists_eq_count_pos. Qed.

(* Interactions with [mem] *)

Lemma count_pos_eq_exists_mem : forall P l,
  (count P l > 0) = (exists x, mem x l /\ P x).
Proof using.
  intros. rewrite <- LibList.count_pos_eq_exists_mem.
  unfold count. rewrite abs_nonneg; math.
Qed.

Lemma count_pos_of_mem : forall x P l,
  mem x l ->
  P x ->
  count P l > 0.
Proof using. introv. rewrite* count_pos_eq_exists_mem. Qed.

Lemma exists_mem_of_count_pos : forall P l,
  count P l > 0 ->
  exists x, mem x l /\ P x.
Proof using. introv. rewrite* count_pos_eq_exists_mem. Qed.

End Count.

Opaque count.

#[global] Hint Rewrite count_nil count_cons count_app count_last count_rev
  : rew_listx.


(* ---------------------------------------------------------------------- *)
(** * [card], with result as [nat], as typeclass *)

(** Note that [card] produces a [nat], whereas [length] produces an [int].
    Currently, in practice, we use [LibList.length] rather than [card]. *)

Definition card_impl A (l:list A) : nat :=
  LibList.length l.

#[global]
Instance card_inst : forall A, BagCard (list A).
Proof using. constructor. rapply (@card_impl A). Defined.

Global Opaque card_inst.


(* ---------------------------------------------------------------------- *)
(** * Hints for [rew_array] and [rew_array_nocase] *)

(** [rew_array_nocase] is a light normalization tactic for array *)

#[global] Hint Rewrite @read_make @length_make @length_update @read_update_same
  : rew_array_nocase.

(** [rew_array] is a normalization tactic for array, which introduces
    case analyses for all read-on-update operations. *)

#[global] Hint Rewrite @read_make @length_make @length_update @read_update_same
  @read_update_case @read_cons_case @read_last_case : rew_array.



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

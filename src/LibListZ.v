(**************************************************************************
* TLC: A library for Coq                                                  *
* Lists accessed with integers (not nat) and using LibBag typeclasses     *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import LibTactics LibLogic LibOperation LibReflect
  LibProd LibNat LibInt LibOption LibWf.
Require Export LibList LibNat.
Require Import LibInt.
Require Export LibBag.

Open Local Scope comp_scope.


(* ********************************************************************** *)
(** * List operations using indices in Z *)

Section Zindices.
Variables A : Type.
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types i : int.
Ltac auto_tilde ::= eauto with maths.


(* ---------------------------------------------------------------------- *)
(** * Definitions *)

(** Functions *)

Definition length (l:list A) :=
  (length l) : int.

Definition nth `{Inhab A} (i:int) (l:list A) :=
  If i < 0 then arbitrary else nth (abs i) l.

Definition update (i:int) (v:A) (l:list A) :=
  If i < 0 then l else LibList.update (abs i) v l.

Definition make (n:int) (v:A) :=
  If n < 0 then arbitrary else make (abs n) v.

End Zindices.


(** Automation for [math], to unfold [length] *)

Lemma LibListZ_length_def : forall A (l:list A),
  length l = LibList.length l.
Proof using. auto. Qed.

Hint Rewrite LibListZ_length_def : rew_maths.

(* DEMO: *)

Goal forall A (l : list A), 0 <= length l.
Proof. intros. math. Qed.

Goal forall (l : list Z) (s n : int),
     s <= n -> s = length l -> n >= 0.
Proof. intros. math. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Typeclasses read & update operations, binds and index predicates *)

(** Note: we also define [card] as [length], but we use [length] everywhere
    in the specifications. *)

Definition card_impl A (l:list A) : nat :=
  LibList.length l.
  (* todo: should it return a nat or an int? might change... *)

Definition read_impl `{Inhab A} (l:list A) (i:int) : A :=
  nth i l.

Definition update_impl A (l:list A) (i:int) (v:A) : list A :=
  update i v l.

Definition index_impl A (l:list A) (i:int) : Prop :=
  index (LibList.length l : int) i.


Instance card_inst : forall A, BagCard (list A).
 constructor. rapply (@card_impl A). Defined.
Instance read_inst : forall `{Inhab A}, BagRead int A (list A).
 constructor. rapply (@read_impl A H). Defined.
Instance update_inst : forall A, BagUpdate int A (list A).
  constructor. rapply (@update_impl A). Defined.
Instance index_inst : forall A, BagIndex int (list A).
  constructor. rapply (@index_impl A). Defined.

Global Opaque card_inst read_inst update_inst index_inst.

(* LATER
Definition binds_impl A (l:list A) (i:int) (v:A) : Prop :=
  index_impl l i /\ nth i l = v.
  (* deprecated:  ZNth i l v. *)
Instance binds_inst : forall A, BagBinds int A (list A).
  constructor. rapply (@binds_impl A). Defined.
Global Opaque binds_inst
*)

(* ---------------------------------------------------------------------- *)
(** * Properties of length *)

Section LengthProperties.
Variable A : Type.
Implicit Types l : list A.
Ltac auto_tilde ::= eauto with maths.

Lemma length_nonneg : forall (l: list A), 0 <= length l.
Proof using. intros. math. Qed.
Lemma length_nil :
  length (@nil A) = 0.
Proof using. auto. Qed.
Lemma length_cons : forall x l,
  length (x::l) = 1 + length l.
Proof using. intros. unfold length. rew_length~. Qed.
Lemma length_singleton: forall (x : A), length (x :: nil) = 1.
Proof using. reflexivity. Qed.
Lemma length_app : forall l1 l2,
  length (l1 ++ l2) = length l1 + length l2.
Proof using. intros. unfold length. rew_length~. Qed.
Lemma length_last : forall x l,
  length (l & x) = 1 + length l.
Proof using. intros. unfold length. rew_length~. Qed.
Lemma length_zero_inv : forall l,
  length l = 0 -> l = nil.
Proof using. intros. unfolds length. applys~ LibList.length_zero_inv. Qed.
Lemma length_tail : forall l,
  l <> nil -> length (tail l) = length l - 1.
Proof using. induction l; intros; simpl; unfold length; rew_length. congruence. math. Qed.
Lemma length_tail_le : forall l,
  length (tail l) <= length l.
Proof using. destruct l; simpl; unfold length; rew_length; math. Qed.
Lemma length_le_1_implies_nil_tail : forall l,
  length l <= 1 -> tail l = nil.
Proof using.
  intros. destruct l; eauto.
  simpl. unfold length in *. rew_length in *.
  eapply length_zero_inv. math.
Qed.
Lemma abs_length:
  forall i l,
  i = length l ->
  abs i = LibList.length l.
Proof.
  unfold length. intros. subst.
  generalize (LibList.length l). clear A l. (* for clarity *)
  rew_maths. eapply Zabs2Nat.id.
Qed.

End LengthProperties.

Hint Rewrite length_nil length_cons length_app
 length_last length_rev : rew_length.
Hint Rewrite length_nil length_cons length_app
 length_last length_rev : rew_list.


(* ---------------------------------------------------------------------- *)
(** * Properties of zmake *)

Section MakeProperties.
Transparent read_inst.

Lemma read_make : forall `{Inhab A} (i n:int) (v:A),
  index n i -> (make n v)[i] = v.
Proof using.
  introv N. rewrite int_index_def in N. unfold make, read_inst, read_impl, nth.
  case_if. math. simpl. case_if. math.
  applys nth_make. forwards: Zabs_nat_lt i n; try math.
Qed.

Lemma length_make : forall A (n:int) (v:A),
  n >= 0 ->
  length (make n v) = n :> int.
Proof using.
  introv N. unfold make. case_if. math.
  unfold length. rewrite LibList.length_make.
  rewrite~ abs_pos.
Qed.

Lemma cons_make: forall n A (x : A), 0 < n -> x :: make (n - 1) x = make n x.
Proof.
  intros.
  unfold make. do 2 (case_if; [ math | ]).
  (* This is really painful. *)
  rewrite abs_minus by math.
  change (abs 1) with 1%nat.
  assert (0 < abs n)%nat.
  { change 0%nat with (abs 0%Z).
    eapply Zabs.Zabs_nat_lt.
    math. }
  eapply LibList.cons_make.
  math.
Qed.

End MakeProperties.


(* -------------------------------------------------------------------------- *)

(* Properties of [read]. *)

Section ReadProperties.
Transparent read_inst.

Context (A : Type) `{Inhab A}.

Lemma read_zero:
  forall x (xs : list A),
  (x :: xs)[0] = x.
Proof.
  intros. unfold read, read_inst, read_impl, nth.
  case_if; [ math | ]. reflexivity.
Qed.

Lemma read_succ:
  forall x (xs : list A) i,
  0 <= i < length xs ->
  (x :: xs)[i + 1] = xs[i].
Proof.
  intros. unfold read, read_inst, read_impl, nth, LibList.nth.
  do 2 (case_if; [ math | ]).
  change (i + 1) with (Z.succ i).
  rewrite Zabs2Nat.inj_succ by math.
  reflexivity.
Qed.

End ReadProperties.

(* ---------------------------------------------------------------------- *)
(* Extensional equality between two lists. *)

Lemma ext_eq:
  forall A `{Inhab A} (xs ys : list A),
  length xs = length ys ->
  (forall i, 0 <= i < length xs -> xs[i] = ys[i]) ->
  xs = ys.
Proof.
  induction xs; destruct ys; simpl; introv Heq Hread;
  try solve [ eauto | false ]. f_equal.
  (* The head. *)
  { specializes Hread 0.
    repeat rewrite read_zero in Hread.
    repeat rewrite length_cons in Hread.
    eapply Hread.
    forwards: length_nonneg xs. math. }
  (* The tail. *)
  { repeat rewrite length_cons in *.
    eapply IHxs. math. intros i Hi.
    specializes Hread (i + 1).
    do 2 rewrite read_succ in Hread by math.
    eapply Hread. math. }
Qed.

Lemma ext_eq_index:
  forall A `{Inhab A} (xs ys : list A),
  length xs = length ys ->
  (forall i, index xs i -> xs[i] = ys[i]) ->
  xs = ys.
Proof.
  eauto using ext_eq.
Qed.

(* ---------------------------------------------------------------------- *)
(** * Properties of update *)

Section UpdateProperties.
Transparent index_inst read_inst update_inst.

Lemma index_def : forall A (l:list A) i,
  index l i = index (length l : int) i.
Proof using. auto. Qed.

Lemma length_update : forall A (l:list A) (i:int) (v:A),
  length (l[i:=v]) = length l.
Proof using.
  intros. unfold update_inst, update_impl, length, update. simpl.
  case_if. math. rewrite~ length_update.
Qed.

Lemma index_update_eq : forall A (l:list A) i j (v:A),
  index (l[j:=v]) i = index l i.
Proof using. intros. rewrite index_def in *. rewrite~ length_update. Qed.

Lemma index_update : forall A (l:list A) i j (v:A),
  index l i -> index (l[j:=v]) i.
Proof using. intros. rewrite~ index_update_eq. Qed.

Lemma read_update_case : forall `{Inhab A} (l:list A) (i j:int) (v:A),
  index l j -> l[i:=v][j] = (If i = j then v else l[j]).
Proof using.
  introv. unfold index_inst, index_impl, update_inst, update_impl, update,
    read_inst, read_impl, nth. simpl. introv N. rewrite int_index_def in N.
  case_if. math.
  case_if. case_if. auto. case_if.
    rewrite~ nth_update_eq. apply nat_int_lt. rewrite abs_pos; try math.
    rewrite~ nth_update_neq. apply nat_int_lt. rewrite abs_pos; try math.
      apply nat_int_neq. rewrite abs_pos; try math. rewrite abs_pos; try math.
Qed.

Lemma read_update_eq : forall `{Inhab A} (l:list A) (i:int) (v:A),
  index l i -> (l[i:=v])[i] = v.
Proof using. introv N. rewrite~ read_update_case. case_if~. Qed.

Lemma read_update_neq : forall `{Inhab A} (l:list A) (i j:int) (v:A),
  index l j -> (i <> j) -> (l[i:=v])[j] = l[j].
Proof using. introv N. rewrite~ read_update_case. case_if; auto_false~. Qed.

Lemma update_update_eq : forall `{Inhab A} (l:list A) (i:int) (v w:A),
  index l i -> l[i:=v][i:=w] = l[i:=w].
Proof using.
  intros. eapply ext_eq_index; repeat rewrite length_update.
  { reflexivity. }
  intros j.
  repeat rewrite index_update_eq.
  intros Hj.
  repeat rewrite read_update_case by eauto using index_update.
  case_if; reflexivity.
Qed.

Lemma update_update_neq : forall `{Inhab A} (l:list A) (i j:int) (v w:A),
  index l i -> index l j -> i <> j -> l[i:=v][j:=w] = l[j:=w][i:=v].
Proof using.
  intros. eapply ext_eq_index; repeat rewrite length_update.
  { reflexivity. }
  intros k.
  repeat rewrite index_update_eq.
  intros Hk.
  repeat rewrite read_update_case by eauto using index_update.
  repeat case_if; reflexivity.
Qed.

Lemma update_app_right:
  forall A ys j xs i ij (v : A),
  i = length xs ->
  0 <= j ->
  ij = i + j ->
  (xs ++ ys)[ij:=v] = xs ++ ys[j:=v].
Proof.
  intros. subst ij.
  unfold LibBag.update, update_inst, update_impl.
  unfold update. do 2 (case_if; [ math | ]).
  eapply LibList.update_app_right with (i := abs i).
  { eauto using abs_length. }
  { eapply Zabs2Nat.inj_add; math. }
Qed.

Lemma update_app_right_here:
  forall A i (xs ys : list A) x y,
  i = length xs ->
  (xs ++ y :: ys)[i := x] = xs & x ++ ys.
Proof.
  intros.
  unfold LibBag.update, update_inst, update_impl.
  unfold update. case_if; [ math | ].
  eapply LibList.update_app_right_here.
  eauto using abs_length.
Qed.

Lemma read_cons_case : forall `{IA:Inhab A} (l:list A) (i:int) (v:A),
  (v::l)[i] = (If i = 0 then v else l[i-1]).
Proof using.
  introv. simpl. unfold read_impl, nth.
  case_if.
  - case_if. math. case_if~. math.
  - case_if~. case_if. math. rewrite~ abs_spos. math.
Qed.

Lemma read_last_case : forall `{IA:Inhab A} (l:list A) (i:int) (v:A),
  (l & v)[i] = (If i = LibList.length l then v else l[i]).
Proof using.
  introv. simpl. unfold read_impl, nth.
  case_if.
  - case_if~; math.
  - admit. (* lemmas missing about "&" and LibList.nth *)
Qed.

End UpdateProperties.


(* ---------------------------------------------------------------------- *)
(** * Normalization tactics *)

(** [rew_arr] is a light normalization tactic for array *)

(* TODO: rename to [rew_array_nocase] *)
Hint Rewrite @read_make @length_make @length_update @read_update_eq
  : rew_arr.

Tactic Notation "rew_arr" :=
  autorewrite with rew_arr.
Tactic Notation "rew_arr" "in" hyp(H) :=
  autorewrite with rew_arr in H.
Tactic Notation "rew_arr" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_arr).
  (* autorewrite with rew_arr in *. *)

Tactic Notation "rew_arr" "~" :=
  rew_arr; auto_tilde.
Tactic Notation "rew_arr" "*" :=
  rew_arr; auto_star.
Tactic Notation "rew_arr" "~" "in" hyp(H) :=
  rew_arr in H; auto_tilde.
Tactic Notation "rew_arr" "*" "in" hyp(H) :=
  rew_arr in H; auto_star.
Tactic Notation "rew_arr" "~" "in" "*" :=
  rew_arr in *; auto_tilde.
Tactic Notation "rew_arr" "*" "in" "*" :=
  rew_arr in *; auto_star.

(** [rew_array] is a normalization tactic for array *)

Hint Rewrite @read_make @length_make @length_update @read_update_eq
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

(* ---------------------------------------------------------------------- *)
(** * Valid index predicate *)

Section IndexProperties.
Transparent index_inst.

(* [index_def] : proven above *)

(* [index_update] : proven above *)

Lemma index_length_unfold : forall A (l:list A) i,
  index (length l : int) i -> index l i.
Proof using. introv H. rewrite* index_def. Qed.

Lemma index_length_eq : forall A (l:list A) (n:int) i,
  index n i -> n = length l -> index l i.
Proof using. intros. subst. rewrite~ index_def. Qed.

Lemma index_bounds : forall A (l:list A) i,
  index l i = (0 <= i < length l).
Proof using. auto. Qed.

Lemma index_bounds_impl : forall A (l:list A) i,
  0 <= i < length l -> index l i.
Proof using. intros. rewrite~ index_bounds. Qed.

Lemma index_zmake : forall A n i (v:A),
  index n i -> index (make n v) i.
Proof using.
  introv H. rewrite index_def. rewrite int_index_def in H.
  rewrite~ length_make. math.
Qed.

End IndexProperties.


(* ---------------------------------------------------------------------- *)
(** * count *)

(* UNDER CONSTRUCTION *)

(* TODO: complete definitions and proofs, which are used by CFML/Dijstra *)

Require Import LibWf.

(* TODO: implement a non-decidable version of count *)

Axiom count : (* UNDER CONSTRUCTION *)
  forall A (P:A->Prop) (l:list A), int.

(* currently not used
  Axiom count_make : forall A (f:A->Prop) n v,
    count f (make n v) = (If f v then n else 0).
*)

Axiom count_update : (* UNDER CONSTRUCTION *)
  forall `{Inhab A} (P:A->Prop) (l:list A) (i:int) v,
  index l i ->
  count P (l[i:=v]) = count P l
    - (If P (l[i]) then 1 else 0)
    + (If P v then 1 else 0).

Axiom count_bounds : (* UNDER CONSTRUCTION *)
  forall `{Inhab A} (l:list A) (P:A->Prop),
  0 <= count P l <= length l.

(** The following lemma is used to argue that the update to a sequence,
    when writing a value that satisfies [P] in place of one that did not
    satisfy [P], decreases the total number of values that satisfying
    [P] in the sequence. *)

Lemma count_upto : forall `{Inhab A} (P:A->Prop) (l:list A) (n i:int) (v:A),
  ~ P (l[i]) -> P v -> index l i -> (length l <= n)%Z ->
  upto n (count P (l[i:=v])) (count P l).
Proof using.
  introv Ni Pv Hi Le. forwards K: (count_bounds (l[i:=v]) P). split.
  rewrite length_update in K. math.
  lets M: (@count_update A _). rewrite~ M. clear M.
  do 2 (case_if; tryfalse). math.
Qed.



(* ---------------------------------------------------------------------- *)
(* LATER:

Lemma isTrue_eq_list : forall A {IA:Inhab A} (L1 L2:list A),
  len L1 = len L2 ->
  ((forall i, index (len L1) i -> L1[i] = L2[i]) ->
  (L1 = L2)).

*)





(* ********************************************************************** *)
(** * DEPRECATED -- List predicates using indices in Z *)

Section ZindicesOld.
Variables A : Type.
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types i : int.
Ltac auto_tilde ::= eauto with maths.

(* ---------------------------------------------------------------------- *)
(** * DEPRECATED *)

(** Predicates *)

Definition ZInbound i l :=
  0 <= i /\ i < length l.

Definition ZNth i l x :=
  Nth (abs i) l x /\ 0 <= i.

Definition ZUpdate i x l l' :=
  Update (abs i) x l l' /\ 0 <= i.


(* ---------------------------------------------------------------------- *)
(** * DEPRECATED -- Znth *)

Lemma ZNth_here : forall i x l,
  i = 0 -> ZNth i (x::l) x.
Proof using. intros. subst. split~. constructor. Qed.

Lemma ZNth_zero : forall x l,
  ZNth 0 (x::l) x.
Proof using. intros. apply~ ZNth_here. Qed.

Lemma ZNth_next : forall i j x y l,
  ZNth j l x -> i = j+1 -> ZNth i (y::l) x.
Proof using.
  introv [H P] M. subst. split~.
  applys_eq* Nth_next 3. rew_abs_pos~.
Qed.

Lemma ZNth_app_l : forall i x l1 l2,
  ZNth i l1 x -> ZNth i (l1 ++ l2) x.
Proof using. introv [H P]. split~. apply~ Nth_app_l. Qed.

Lemma ZNth_app_r : forall i j x l1 l2,
  ZNth j l2 x -> i = j + length l1 -> ZNth i (l1 ++ l2) x.
Proof using.
  introv [H P]. unfold length. split~. subst.
  apply* Nth_app_r. rew_abs_pos~.
Qed.

Lemma ZNth_nil_inv : forall i x,
  ZNth i nil x -> False.
Proof using. introv [H P]. apply* Nth_nil_inv. Qed.

Lemma ZNth_cons_inv : forall i x l,
  ZNth i l x ->
     (exists q, l = x::q /\ i = 0)
  \/ (exists y q j, l = y::q /\ ZNth j q x /\ i = j+1).
Proof using.
  introv [H P]. forwards~: (@abs_pos i).
  destruct (Nth_cons_inv H); unpack.
  left. exists___. split~.
  right. exists___. splits~.
   split. rewrite* abs_pos_nat. math.
   math.
Qed.

Lemma ZNth_inbound : forall i l,
   ZInbound i l -> exists x, ZNth i l x.
Proof using.
  introv [P U]. unfolds length. gen_eq n: (abs i).
  gen i l. induction n; intros;
    forwards~: (@abs_pos i); destruct l; rew_length in U; try math.
  math_rewrite (i = 0). exists __. split~. constructor.
  forwards~ [x [M P']]: (>> IHn (i-1) l).
    forwards~: (@abs_spos i).
    exists x. split~. rewrite~ (@abs_spos i). constructor~.
Qed.


(* ---------------------------------------------------------------------- *)
(** * DEPRECATED -- ZInbound *)

Lemma ZInbound_zero : forall x l,
  ZInbound 0 (x::l).
Proof using. split; unfold length; rew_list~. Qed.

Lemma ZInbound_zero_not_nil : forall x l,
  l <> nil -> ZInbound 0 l.
Proof using.
  intros. split~. unfold length.
  destruct l; tryfalse. rew_list~.
Qed.

Lemma ZInbound_cons : forall i j x l,
  ZInbound j l -> j = i-1 -> ZInbound i (x::l).
Proof using. introv [P U] H. split; rew_list~. Qed.

Lemma ZInbound_nil_inv : forall i,
  ZInbound i nil -> False.
Proof using. introv [P U]. rew_list in U. math. Qed.

Lemma ZInbound_cons_inv : forall i x l,
  ZInbound i (x::l) -> i = 0 \/ (i <> 0 /\ ZInbound (i-1) l).
Proof using.
  introv [P U]. rew_length in U. tests: (i = 0).
    left~.
    right~. split. math. split~.
Qed.

Lemma ZInbound_cons_pos_inv : forall i x l,
  ZInbound i (x::l) -> i <> 0 -> ZInbound (i-1) l.
Proof using.
  introv H P. destruct* (ZInbound_cons_inv H).
Qed.

Lemma ZInbound_one_pos_inv : forall i x,
  ZInbound i (x::nil) -> i <> 0 -> False.
Proof using.
  intros. eapply ZInbound_nil_inv. apply* ZInbound_cons_pos_inv.
Qed.

Lemma ZInbound_app_l_inv : forall i l1 l2,
  ZInbound i (l1++l2) -> i < length l1 -> ZInbound i l1.
Proof using. introv [P U] H. split~. Qed.

Lemma ZInbound_app_r_inv : forall i j l1 l2,
  ZInbound j (l1++l2) -> j = length l1 + i -> i >= 0 -> ZInbound i l2.
Proof using. introv [P U] R H. rew_length in U. split~. Qed.


(* ---------------------------------------------------------------------- *)
(** * DEPRECATED -- ZUpdate *)

Lemma ZUpdate_here : forall x y l,
  ZUpdate 0 x (y::l) (x::l).
Proof using. split~. apply Update_here. Qed.

Lemma ZUpdate_cons : forall i j x y l l',
  ZUpdate j x l l' -> i = j+1 -> ZUpdate i x (y::l) (y::l').
Proof using.
  introv [U P] H. split~. applys_eq~ Update_cons 4.
  subst. rew_abs_pos~.
Qed.

Lemma ZUpdate_app_l : forall i x l1 l1' l2,
  ZUpdate i x l1 l1' -> ZUpdate i x (l1++l2) (l1'++l2).
Proof using. introv [U P]. split~. apply~ Update_app_l. Qed.

Lemma ZUpdate_app_r : forall i j x l1 l2 l2',
  ZUpdate j x l2 l2' -> i = j + length l1 -> ZUpdate i x (l1++l2) (l1++l2').
Proof using.
  introv [U P] H. unfolds length. split~. apply~ Update_app_r.
  subst. rew_abs_pos~.
Qed.

Lemma ZUpdate_not_nil : forall i x l1 l2,
  ZUpdate i x l1 l2 -> l2 <> nil.
Proof using. introv [U P]. apply~ Update_not_nil. Qed.

Lemma ZUpdate_length : forall i x l l',
  ZUpdate i x l l' -> length l = length l'.
Proof using.
  introv [U P]. unfolds length.
  forwards~: Update_length.
Qed.


End ZindicesOld.

(* -------------------------------------------------------------------------- *)

(* The [prefix] ordering on lists has been defined in [LibList]. Here, we
   provide an alternate definition, as well as more properties. *)

(* TEMPORARY characterize [prefix] as pointwise equality *)

Section Prefix.

Variable A : Type.
Implicit Types xs ys : list A.

Lemma le_implies_ge: forall x y, x <= y -> y >= x.
Proof. math. Qed.

Local Hint Resolve le_implies_ge length_nonneg.

(* [prefix], [snoc], and read access. *)

Lemma prefix_read:
  forall `{Inhab A} ys xs y,
  prefix (ys & y) xs ->
  y = xs[length ys].
Proof using.
  intros.
  change (xs[length ys]) with (nth (length ys) xs).
  unfold nth. case_if as Hop; [ | clear Hop ].
  { false. forwards: length_nonneg ys. math. }
  unfold LibList.nth.
  generalize dependent xs.
  generalize dependent ys. unfold prefix.
  induction ys; intros xs [ zs ? ]; rew_list in *.
  (* Base case. *)
  { change (abs 0) with (0%nat).
    subst xs. reflexivity. }
  (* Inductive case. *)
  { rewrite abs_plus by first [ math | eauto ].
    change (abs 1) with (1%nat).
    destruct xs as [ | x xs ]; [ congruence | ].
    simpl. eapply IHys. exists zs. rew_list. congruence. }
Qed.

(* [prefix] and [length]. *)

Lemma prefix_length:
  forall ys xs,
  prefix ys xs ->
  length ys <= length xs.
Proof using.
  intros ys xs [ zs ? ]. subst xs. rew_list.
  assert (length zs >= 0). { eauto. }
  math.
Qed.

Lemma prefix_snoc_length:
  forall ys y xs,
  prefix (ys & y) xs ->
  length ys < length xs.
Proof using.
  intros ys y xs [ zs ? ]. subst xs. rew_list.
  assert (length zs >= 0). { eauto. }
  math.
Qed.

End Prefix.

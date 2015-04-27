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

(** Set up specialized automation for this section *)
Ltac auto_tilde ::= eauto with maths.


(* ---------------------------------------------------------------------- *)
(** * Definitions *)

(** Functions *)

Definition znth `{Inhab A} (i:int) (l:list A) :=
  If i < 0 then arbitrary else nth (abs i) l. 

Definition zupdate (i:int) (v:A) (l:list A) :=
  If i < 0 then l else LibList.update (abs i) v l.

Definition zmake (n:int) (v:A) :=
  If n < 0 then arbitrary else make (abs n) v.

(** Predicates *)

Definition ZInbound i l := 
  0 <= i /\ i < length l.

Definition ZNth i l x := 
  Nth (abs i) l x /\ 0 <= i.

Definition ZUpdate i x l l' :=
  Update (abs i) x l l' /\ 0 <= i.


(* ---------------------------------------------------------------------- *)
(** * Znth *)

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
  introv [H P]. split~. subst. 
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
  introv [P U]. gen_eq n: (abs i). 
  gen i l. induction n; intros; 
    forwards~: (@abs_pos i); destruct l; rew_length in U; try math.
  math_rewrite (i = 0). exists __. split~. constructor.
  forwards~ [x [M P']]: (>> IHn (i-1) l).
    forwards~: (@abs_spos i).
    exists x. split~. rewrite~ (@abs_spos i). constructor~.
Qed.


(* ---------------------------------------------------------------------- *)
(** * ZInbound *)

Lemma ZInbound_zero : forall x l,
  ZInbound 0 (x::l).
Proof using. split; rew_list~. Qed. 

Lemma ZInbound_zero_not_nil : forall x l,
  l <> nil -> ZInbound 0 l.
Proof using. intros. split~. destruct l; tryfalse. rew_list~. Qed.

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
(** * ZUpdate *)

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
  introv [U P] H. split~. apply~ Update_app_r. 
  subst. rew_abs_pos~.
Qed.

Lemma ZUpdate_not_nil : forall i x l1 l2,
  ZUpdate i x l1 l2 -> l2 <> nil.
Proof using. introv [U P]. apply~ Update_not_nil. Qed.

Lemma ZUpdate_length : forall i x l l',
  ZUpdate i x l l' -> length l = length l'.
Proof using. introv [U P]. apply~ Update_length. Qed. 

End Zindices.


(* ---------------------------------------------------------------------- *)
(** ** Typeclasses read & update operations, binds and index predicates *)

(** Note: we also define [card] as [length], but we use [length] everywhere
    in the specifications. *)

Definition card_impl A (l:list A) : nat :=
  length l.

Definition read_impl `{Inhab A} (l:list A) (i:int) : A :=
  znth i l.

Definition update_impl A (l:list A) (i:int) (v:A) : list A :=
  zupdate i v l.

Definition binds_impl A (l:list A) (i:int) (v:A) : Prop := 
  ZNth i l v.

Definition index_impl A (l:list A) (i:int) : Prop :=
  index (LibList.length l : int) i.

Instance card_inst : forall A, BagCard (list A).
 constructor. rapply (@card_impl A). Defined.
Instance read_inst : forall `{Inhab A}, BagRead int A (list A).
 constructor. rapply (@read_impl A H). Defined.
Instance update_inst : forall A, BagUpdate int A (list A).
  constructor. rapply (@update_impl A). Defined.
Instance binds_inst : forall A, BagBinds int A (list A).
  constructor. rapply (@binds_impl A). Defined.
Instance index_inst : forall A, BagIndex int (list A).
  constructor. rapply (@index_impl A). Defined.

Global Opaque card_inst read_inst update_inst binds_inst index_inst.


(* ---------------------------------------------------------------------- *)
(** * Properties of zmake *)

Section MakeProperties.
Transparent read_inst.

Lemma read_zmake : forall `{Inhab A} (i n:int) (v:A),
  index n i -> (zmake n v)\(i) = v.
Proof using.
  introv N. rewrite int_index_def in N. unfold zmake, read_inst, read_impl, znth.
  case_if. math. simpl. case_if. math.
  applys nth_make. forwards: Zabs_nat_lt i n; try math.
Qed.

Lemma length_zmake : forall A (n:int) (v:A),
  n >= 0 ->
  length (zmake n v) = n :> int.
Proof using.
  introv N. unfold zmake. case_if. math.
  rewrite length_make. rewrite~ abs_pos.
Qed.

End MakeProperties.


(* ---------------------------------------------------------------------- *)
(** * Properties of update *)

Section UpdateProperties.
Transparent index_inst read_inst update_inst.

Lemma length_update : forall A (l:list A) (i:int) (v:A),
  length (l\(i:=v)) = length l.
Proof using.
  intros. unfold update_inst, update_impl, zupdate. simpl.
  case_if. math. rewrite~ length_update.
Qed.

Lemma read_update_eq : forall `{Inhab A} (l:list A) (i:int) (v:A),
  index l i -> (l\(i:=v))\(i) = v.
Proof using. 
  introv. unfold index_inst, index_impl, update_inst, update_impl, zupdate,
    read_inst, read_impl, znth. simpl. introv N. rewrite int_index_def in N.
  case_if. math.
  rewrite~ nth_update_eq. apply nat_int_lt. rewrite abs_pos; try math.
Qed.

Lemma read_update_neq : forall `{Inhab A} (l:list A) (i j:int) (v:A),
  index l j -> (i <> j) -> (l\(i:=v))\(j) = l\(j).
Proof using.
  introv. unfold index_inst, index_impl, update_inst, update_impl, zupdate,
    read_inst, read_impl, znth. simpl. introv N E. rewrite int_index_def in N.
  case_if. math. case_if. auto.
  rewrite~ nth_update_neq. apply nat_int_lt. rewrite abs_pos; try math.
    apply nat_int_neq. rewrite abs_pos; try math. rewrite abs_pos; try math.
Qed.

End UpdateProperties.


(* ---------------------------------------------------------------------- *)
(** * Normalization tactics *)

(** [rew_arr] is a light normalization tactic for array *)

Hint Rewrite @read_update_eq : rew_arr.

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

(** [rew_array] is a more aggressive normalization tactic for array *)
(* TODO: rename into [rew_arr_all] *)

Hint Rewrite @read_zmake @length_update @read_update_eq
  @read_update_neq : rew_array.

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


(* ---------------------------------------------------------------------- *)
(** * Valid index predicate *)

Section IndexProperties.
Transparent index_inst.

Lemma index_def : forall A (l:list A) i,
  index l i = index (length l : int) i.
Proof using. auto. Qed. 

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

Lemma index_update : forall A (l:list A) i j (v:A),
  index l i -> index (l\(j:=v)) i.
Proof using. intros. rewrite index_def in *. rewrite~ length_update. Qed.

Lemma index_zmake : forall A n i (v:A),
  index n i -> index (zmake n v) i.
Proof using.
  introv H. rewrite index_def. rewrite int_index_def in H.
  rewrite~ length_zmake. math.
Qed.

End IndexProperties.


(* ---------------------------------------------------------------------- *)
(** * count *)

(* TODO: complete definitions and proofs, which are used by CFML/Dijstra *)

Require Import LibWf.

(* TODO: implement a non-decidable version of count *)

Parameter zcount : forall A (P:A->Prop) (l:list A), int.

(* currently not used
Parameter count_make : forall A (f:A->Prop) n v,
  count f (make n v) = (If f v then n else 0).
*)

Parameter zcount_update : forall `{Inhab A} (P:A->Prop) (l:list A) (i:int) v,
  index l i ->
  zcount P (l\(i:=v)) = zcount P l
    - (If P (l\(i)) then 1 else 0)
    + (If P v then 1 else 0).

Parameter zcount_bounds : forall `{Inhab A} (l:list A) (P:A->Prop),
  0 <= zcount P l <= length l.

(** The following lemma is used to argue that the update to a sequence,
    when writing a value that satisfies [P] in place of one that did not
    satisfy [P], decreases the total number of values that satisfying 
    [P] in the sequence. *)

Lemma zcount_upto : forall `{Inhab A} (P:A->Prop) (l:list A) (n i:int) (v:A),
  ~ P (l\(i)) -> P v -> index l i -> (length l <= n)%Z ->
  upto n (zcount P (l\(i:=v))) (zcount P l).
Proof using.
  introv Ni Pv Hi Le. forwards K: (zcount_bounds (l\(i:=v)) P). split.
  rewrite length_update in K. math.
  lets M: (@zcount_update A _). rewrite~ M. clear M. 
  do 2 (case_if; tryfalse). math.
Qed.


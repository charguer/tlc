(*-- TODO COMPLETE CLEANUP --*)

(**************************************************************************
* TLC: A library for Coq                                                  *
* Sub-lists                                                               *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import Coq.Classes.Morphisms. (* for [Proper] instances *)
From TLC Require Import LibTactics LibLogic LibReflect LibOperation
 LibProd LibOption LibNat LibInt LibWf LibMonoid LibRelation LibList.
Local Open Scope nat_scope.
Local Open Scope comp_scope.
Global Close Scope list_scope.


(* -------------------------------------------------------------------------- *)

(* The [prefix] ordering on lists. *)

Section Prefix.

Variables (A : Type).

(* A definition in terms of concatenation. See also [LibListZ]. *)

Definition prefix (ys xs : list A) :=
  exists zs, ys ++ zs = xs.

  (* --TODO one could give an alternate definition of [prefix] as an
     inductive predicate with two cases: [Nil/Cons] and [Cons/Cons].
     This would give rise to a potentially useful induction principle.
     Or just prove this induction principle directly. *)

(* Ordering. *)

Lemma prefix_reflexive:
  forall xs,
  prefix xs xs.
Proof using.
  intros. exists (@nil A). eapply app_nil_r.
Qed.

Lemma prefix_antisymmetric:
  forall xs ys,
  prefix xs ys ->
  prefix ys xs ->
  xs = ys.
Proof using.
  introv (ws&Ex) (zs&Ey). subst ys. rew_list in *.
  forwards Ey': app_l_eq_self_inv (rm Ey).
  forwards (E1&E2): app_eq_nil_inv (rm Ey').
  subst. rew_list~.
Qed.

Lemma prefix_transitive:
  forall xs ys zs,
  prefix xs ys ->
  prefix ys zs ->
  prefix xs zs.
Proof using.
  introv [ xs' ? ] [ ys' ? ].
  subst. rew_list. unfold prefix. eauto.
Qed.

(* [prefix] and [nil]. *)

Lemma prefix_nil:
  forall xs,
  prefix nil xs.
Proof using.
  intros. exists xs. eapply app_nil_l.
Qed.

Lemma prefix_nil_inverse:
  forall xs,
  prefix xs nil ->
  xs = nil.
Proof using.
  introv (ys&?).
  forwards: app_eq_nil_inv. eauto.
  unpack. eauto.
Qed.

(* [prefix] and [cons]. *)

Lemma prefix_cons_inverse: (* TEMPORARY rename: [prefix_cons_r_inverse] *)
  forall xs y ys,
  prefix xs (y :: ys) ->
  xs = nil \/ exists xs', xs = y :: xs' /\ prefix xs' ys.
Proof using.
  introv (zs&Heq).
  destruct xs; [ eauto | right ].
  rew_list in Heq. injects Heq.
  unfold prefix. eauto.
Qed.

Lemma use_prefix_cons: (* TEMPORARY rename: [prefix_cons_l_inverse] *)
  forall x xs ys,
  prefix (x :: xs) ys ->
  exists ys', ys = x :: ys'.
Proof using.
  introv [ slack ? ]. rew_list in *. exists (xs ++ slack). eauto.
Qed.

Lemma prefix_cons_cons:
  forall x xs1 xs2,
  prefix xs1 xs2 ->
  prefix (x :: xs1) (x :: xs2).
Proof using.
  introv (ys&?). subst. exists ys. rew_list. eauto.
Qed.

Lemma prefix_cons_cons_inverse:
  forall x1 x2 xs1 xs2,
  prefix (x1 :: xs1) (x2 :: xs2) ->
  x1 = x2 /\ prefix xs1 xs2.
Proof using.
  intros.
  forwards: prefix_cons_inverse; eauto.
  branches; unpack; try split; congruence.
Qed.

Lemma prefix_cons_cons_eq:
  forall x xs1 xs2,
  prefix (x :: xs1) (x :: xs2) = prefix xs1 xs2.
Proof using.
  intros. extens. split.
  { eapply prefix_cons_cons_inverse. }
  { eapply prefix_cons_cons. }
Qed.

(* [prefix] and [++]. *)

Lemma prefix_concat:
  forall xs ys zs,
  prefix xs ys ->
  prefix xs (ys ++ zs).
Proof using.
  unfold prefix. introv (ws&?). subst ys.
  exists (ws ++ zs). rew_list. eauto.
Qed.

Lemma prefix_concat_simplify:
  forall xs ys1 ys2,
  prefix ys1 ys2 ->
  prefix (xs ++ ys1) (xs ++ ys2).
Proof using.
  introv (ws&?). subst ys2. exists ws. rew_list. eauto.
Qed.

Lemma eliminate_common_prefix:
  forall xs ys zs,
  prefix (xs ++ ys) (xs ++ zs) ->
  prefix ys zs.
Proof using.
  introv [ slack ? ]. exists slack.
  rew_list in *.
  eauto using app_cancel_l.
Qed.

Lemma prefix_app_r_inverse:
  forall ys1 xs ys2,
  prefix xs (ys1 ++ ys2) ->
  prefix xs ys1 \/
  exists ys2a, xs = ys1 ++ ys2a /\ prefix ys2a ys2.
Proof using.
  induction ys1 as [ | y ys1 ]; simpl; intros.
  { right. exists xs. rew_list in *. eauto. }
  { destruct xs as [ | x xs ].
    { eauto using prefix_nil. }
    { rew_list in *.
      forwards: prefix_cons_cons_inverse. { eauto. } unpack. subst y.
      forwards [ ? | (ys2a&?&?) ]: IHys1. { eauto. }
      { eauto using prefix_cons_cons. }
      { right. eexists ys2a. rew_list. subst xs. eauto. }
    }
  }
Qed.

(* [prefix] and [snoc]. *)

Lemma prove_prefix_snoc:
  forall x xs ys zs,
  xs ++ x :: ys = zs ->
  prefix (xs & x) zs.
Proof using.
  intros. exists ys. rew_list. eauto.
Qed.

Lemma use_prefix_snoc:
  forall x xs ys zs,
  prefix (xs & x) ys ->
  ys = xs ++ zs ->
  exists zs', zs = x :: zs'.
Proof using.
  introv h ?. subst.
  forwards: eliminate_common_prefix h.
  eauto using use_prefix_cons.
Qed.

Lemma prefix_last: (* TEMPORARY should be: use_prefix_snoc *)
  forall x xs ys,
  prefix (xs & x) ys ->
  prefix xs ys.
Proof using.
  introv [ zs ? ]. exists (x :: zs). rew_list in *. eauto.
Qed.

(* [prefix] and [length]. See also [LibListZ]. *)

Lemma prefix_full_inv : forall xs ys,
  length xs = length ys ->
  prefix xs ys ->
  xs = ys.
Proof using. (* TOCLEAN *)
  introv Hl (zs,Hzs).
  asserts E : (zs = nil).
  { destruct zs; try easy.
    apply (f_equal (length (A:=A))) in Hzs.
    rew_list in Hzs. math. }
  subst. rew_list*.
Qed.

Lemma prefix_length:
  forall ys xs,
  prefix ys xs ->
  length ys <= length xs.
Proof using.
  intros ys xs [ zs ? ]. subst xs. rew_list. math.
Qed.

Lemma prefix_snoc_length:
  forall ys y xs,
  prefix (ys & y) xs ->
  length ys < length xs.
Proof using.
  intros ys y xs [ zs ? ]. subst xs. rew_list. math.
Qed.

(* [prefix] and [No_duplicates]. *)

Lemma noduplicates_prefix:
  forall xs ys,
  noduplicates ys ->
  prefix xs ys ->
  noduplicates xs.
Proof using.
  introv ? (zs&?). subst.
  forwards: noduplicates_app_inv; eauto.
  tauto.
Qed.

End Prefix.

#[global]
Hint Resolve
  prefix_reflexive
  prefix_nil
  prefix_cons_cons
  prefix_concat
  prefix_concat_simplify
  prove_prefix_snoc
: prefix.

(* -------------------------------------------------------------------------- *)

Section PrefixClosed.

Variables (A : Type).

Implicit Types xs ys : list A.

(* Prefix-closedness. *)

Definition prefix_closed (P : list A -> Prop) :=
  forall xs ys,
  P ys ->
  prefix xs ys ->
  P xs.

Lemma prefix_closed_nil:
  forall (P : list A -> Prop) xs,
  prefix_closed P ->
  P xs ->
  P nil.
Proof using.
  eauto with prefix.
Qed.

(* Prefix closure. *)

Definition prefix_closure (P : list A -> Prop) : list A -> Prop :=
  fun xs => exists ys, prefix xs ys /\ P ys.

Definition prefix_closure_alt (P : list A -> Prop) : list A -> Prop :=
  fun xs => exists ys, P (xs ++ ys).

Lemma prefix_closure_eq:
  forall P,
  prefix_closure P = prefix_closure_alt P.
Proof using.
  intros. extens; intros xs; split; unfold prefix_closure, prefix_closure_alt, prefix.
  { introv (ys&(zs&?)&?). subst. eauto. }
  { introv (ys&?). eauto. }
Qed.

Lemma prefix_closure_is_prefix_closed:
  forall P,
  prefix_closed (prefix_closure P).
Proof using.
  unfold prefix_closed, prefix_closure.
  introv (zs&?&?). eauto using prefix_transitive.
Qed.

(* The relation [fun xs => prefix xs ys] is the prefix closure of the
   singleton [ys]. Thus, it is prefix-closed. *)

Lemma prefix_closure_singleton:
  forall ys : list A,
  (fun xs => prefix xs ys) = prefix_closure (= ys).
Proof using.
  intros. extens; intros xs. unfold prefix_closure.
  split. eauto. intros (?&?&?). subst. eauto.
Qed.

Lemma prefix_closed_prefix:
  forall ys : list A,
  prefix_closed (fun xs => prefix xs ys).
Proof using.
  intros. rewrite prefix_closure_singleton.
  eapply prefix_closure_is_prefix_closed.
Qed.

End PrefixClosed.


(* -------------------------------------------------------------------------- *)

(* DEPRECATED?

(* The [prefix] ordering on lists has been defined in [LibList]. Here, we
   provide an alternate definition, as well as more properties. *)

(* --TODO characterize [prefix] as pointwise equality *)

Section PrefixMore.

Variables (A : Type).
Implicit Types xs ys : list A.

Lemma le_implies_ge: forall x y, x <= y -> y >= x.
Proof using. math. Qed.

Local Hint Resolve le_implies_ge length_nonneg.

(* [prefix], [snoc], and read access.

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
 *)

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

End PrefixMore.


*)

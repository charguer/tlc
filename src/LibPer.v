(* DEPRECATED

   needs a cleanup and merge into LibRelation.v

*)

(**************************************************************************
* TLC: A library for Coq                                                  *
* Partial equivalence relations                                           *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibBool LibLogic LibRelation LibContainer LibSet.
Module Rel := LibRelation.


(* ********************************************************************** *)
(** * Partial equivalence relations *)

(** [per R] captures the fact that [R] is symmetric and transitive
    relation, that is, a partial equivalence relation *)

Record per A (R:binary A) :=
 { per_sym : sym R;
   per_trans : trans R }.

(** The domain of a PER contains all the points that are related
    to themselves *)

Definition per_dom A (R:binary A) :=
  set_st (fun x => R x x).

(** The empty PER *)

Lemma per_empty:
  forall A,
  per (@LibRelation.empty A).
Proof using.
  unfold LibRelation.empty.
  constructor.
  unfold sym. eauto.
  unfold trans. eauto.
Qed.

Lemma per_dom_empty:
  forall A,
  per_dom (@LibRelation.empty A) = empty.
Proof using.
  reflexivity.
Qed.

(** A singleton PER *)

(* TEMPORARY this is a singleton RELATION and could be in LibRelation. *)
Definition per_single A (a b:A) :=
  fun x y => x = a /\ y = b.

(* TEMPORARY: move this as well to relations *)
Lemma inverse_per_single : forall A (a b:A),
  inverse (per_single a b) = per_single b a.
Proof using.
  intros. applys pred_ext_2. intros. unfold inverse, per_single. autos*.
Qed.


(** Extension of an per [B] with a node [z] *)

Definition per_add_node A (B:binary A) (z:A) :=
  Rel.union B (per_single z z).

(** Extension of an per [B] with an edge between [x] and [y] *)

Definition per_add_edge A (B:binary A) (x y:A) :=
  stclosure (Rel.union B (per_single x y)).

Lemma per_add_edge_le : forall A (B:binary A) a b,
  rel_incl B (per_add_edge B a b).
Proof using. introv. intros x y H. apply stclosure_once. left~. Qed.

Lemma add_edge_already : forall A (B:binary A) a b,
  per B -> B a b -> per_add_edge B a b = B.
Proof using.
  introv P H. extens. intros x y. iff M.
  induction M.
    destruct H0. auto. destruct H0. subst~.
    apply* per_sym.
    apply* per_trans.
  hnf in M.
  apply~ per_add_edge_le.
Qed.

Lemma per_add_edge_per : forall A (R : binary A) a b,
  per R -> per (per_add_edge R a b).
Proof using.
  introv [Rs Rt]. unfold per_add_edge. constructor.
  introv H. applys~ sym_stclosure. applys~ trans_stclosure.
Qed.

Lemma per_dom_add_edge : forall A (B:binary A) x y,
  per B -> x \in per_dom B -> y \in per_dom B ->
  per_dom (per_add_edge B x y) = per_dom B \u \{x} \u \{y}.
Proof using.
  introv [Sy Tr] Bx By. unfold per_add_edge. apply set_ext. intros z.
  unfold Rel.union. unfold per_dom. unfold per_single.
  do 2 rewrite in_union_eq, in_set_st_eq. do 2 rewrite in_single_eq.
  iff H.
  set (a:=z) in H at 1. set (b := z) in H.
  asserts~ K: (a = z \/ b = z). clearbody a b. gen K.
  induction H; introv E.
  left. destruct E; subst; destruct H as [M|[? ?]]; subst*.
  intuition.
  intuition.
  apply stclosure_once. destruct H as [E|[Zx|Zy]]; subst*.
Qed.

Lemma per_add_node_per : forall A (B:binary A) r,
  per B -> per (per_add_node B r).
Proof using.
  introv [Sy Tr]. unfold per_add_node, per_single, Rel.union.
  constructors.
  intros_all. hnf in Sy. intuition.
  intros_all. hnf in Tr. intuition; subst*.
Qed.

Lemma per_dom_add_node : forall A (B:binary A) x,
  per_dom (per_add_node B x) = per_dom B \u \{x}.
Proof using.
  intros. unfold per_add_node. apply set_ext. intros y.
  unfold Rel.union. unfold per_dom. unfold per_single.
  rewrite in_union_eq. rewrite in_single_eq. do 2 rewrite in_set_st_eq.
  intuition.
Qed.

(* --TODO: rename lemma *)
Lemma prove_per_single : forall A (x y : A),
  (per_single x y) x y.
Proof using.
  unfold per_single. eauto.
Qed.

(* --TODO: move instance *)
Global Instance binary_incl : forall A, BagIncl (binary A).
Proof using. constructor. rapply (@rel_incl A A). Defined.


Lemma per_add_edge_covariant : forall A (B1 B2 : binary A) x y,
  incl B1 B2 ->
  incl (per_add_edge B1 x y) (per_add_edge B2 x y).
Proof using.
  unfold binary_incl. unfold per_add_edge.
  (* --TODO: was     eauto using stclosure_le, union_covariant. *)
  introv M. applys covariant_stclosure. applys* covariant_union.
  applys refl_rel_incl.
Qed.

Lemma per_add_edge_symmetric : forall A (B : binary A) x y,
  per_add_edge B y x = per_add_edge B x y.
Proof using.
  unfold per_add_edge. intros.
  (* If two relations have the same symmetric closure, then
     they have the same symmetric-transitive closure. *)
  do 2 rewrite <- tclosure_sclosure_eq_stclosure. f_equal.
  apply pred_ext_2. intros a b. do 2 rewrite sclosure_eq.
  unfold Rel.union, per_single. tauto.
Qed.


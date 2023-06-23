(**************************************************************************
* TLC: A library for Coq                                                  *
* Sets                                                                    *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import Coq.Classes.Morphisms. (* for [Proper] instances *)
From TLC Require Import LibTactics LibLogic LibReflect LibList
  LibOperation LibMonoid LibInt LibNat
  LibEpsilon LibRelation LibMin.
From TLC Require Export LibContainer.


(* ********************************************************************** *)
(** * Construction of sets as predicates *)

(* ---------------------------------------------------------------------- *)
(** ** Basic definitions *)

Definition set (A : Type) := A -> Prop.

Section Operations.
Variables (A B : Type).
Implicit Types x : A.
Implicit Types E F G : set A.

Definition set_st (P:A->Prop) : set A :=
  P.

Definition empty_impl : set A :=
  (fun _ => False).

Definition full_impl : set A :=
  (fun _ => True).

Definition single_impl x :=
  (= x).

Definition in_impl x E :=
  E x.

Definition compl_impl : set A -> set A :=
  @pred_not A. (* -- TODO: as typeclass? *)

Definition union_impl : set A -> set A -> set A :=
  @pred_or A.

Definition inter_impl : set A -> set A -> set A :=
  @pred_and A.

Definition remove_impl : set A -> set A -> set A :=
  fun E F x => E x /\ ~ F x.

Definition incl_impl : set A -> set A -> Prop :=
  @pred_incl A.

Definition disjoint_impl : set A -> set A -> Prop :=
  fun E F : set A => inter_impl E F = empty_impl.

Definition list_repr_impl (E:set A) (l:list A) :=
  noduplicates l /\ forall x, mem x l <-> E x.

Definition to_list (E:set A) :=
  epsilon (list_repr_impl E).

Definition to_set (xs : list A) : set A :=
  set_st (fun x => mem x xs).

Definition list_covers_impl (E:set A) L :=
  forall x, E x -> mem x L.

Definition finite (E:set A) :=
  exists L, list_covers_impl E L.

Definition card_impl (E:set A) : nat :=
  mmin le (fun n => exists L, list_covers_impl E L /\ n = length L).

Definition fold_impl (m:monoid_op B) (f:A->B) (E:set A) :=
  LibList.fold_right (fun x acc => monoid_oper m (f x) acc)
    (monoid_neutral m) (to_list E).

End Operations.


(* ---------------------------------------------------------------------- *)
(** ** Notations to help the typechecker *)

Notation "x \indom E" := (x \in (dom E : set _))
  (at level 39) : container_scope.

Notation "x \notindom E" := (x \notin ((dom E) : set _))
  (at level 39) : container_scope.


(* ---------------------------------------------------------------------- *)
(** ** Inhabited *)

#[global]
Instance Inhab_set : forall A, Inhab (set A).
Proof using. intros. apply (Inhab_of_val (@empty_impl A)). Qed.


(* ---------------------------------------------------------------------- *)
(** ** Notation through typeclasses *)

Lemma in_inst : forall A, BagIn A (set A).
Proof using. constructor. exact (@in_impl A). Defined.

#[global]
Hint Extern 1 (BagIn _ (set _)) => apply in_inst : typeclass_instances.
(* -- LATER: could this be an instance like all others ? *)

#[global]
Instance empty_inst : forall A, BagEmpty (set A).
  constructor. apply (@empty_impl A). Defined.

#[global]
Instance single_inst : forall A, BagSingle A (set A).
  constructor. rapply (@single_impl A). Defined.

#[global]
Instance union_inst : forall A, BagUnion (set A).
  constructor. rapply (@union_impl A). Defined.

#[global]
Instance inter_inst : forall A, BagInter (set A).
  constructor. rapply (@inter_impl A). Defined.

#[global]
Instance remove_inst : forall A, BagRemove (set A) (set A).
  constructor. rapply (@remove_impl A). Defined.

#[global]
Instance incl_inst : forall A, BagIncl (set A).
  constructor. rapply (@incl_impl A). Defined.

#[global]
Instance disjoint_inst : forall A, BagDisjoint (set A).
  constructor. rapply (@disjoint_impl A). Defined.

#[global]
Instance fold_inst : forall A B, BagFold B (A->B) (set A).
  constructor. rapply (@fold_impl A B). Defined.

#[global]
Instance card_inst : forall A, BagCard (set A).
  constructor. rapply (@card_impl A). Defined.

Global Opaque set finite in_inst empty_inst single_inst union_inst inter_inst
  remove_inst incl_inst disjoint_inst card_inst fold_inst.


(* ---------------------------------------------------------------------- *)
(** Exposed definitions for list coverage *)

(** [list_repr E L] asserts that elements of [E] are exactly
    the elements from the list [L]. *)

Definition list_repr A (E:set A) (L:list A) :=
  noduplicates L /\ (forall x, mem x L <-> x \in E).

(** [list_covers E L] asserts that all elements of [E] all
    belong to the list [L]. *)

Definition list_covers A (E:set A) (L:list A) :=
  forall x, x \in E -> mem x L.


(* ---------------------------------------------------------------------- *)
(** ** Notations for building sets *)

(** DISCLAIMER: these definitions are experimental, they'll probably change *)

Declare Scope set_scope.

Notation "\set{ x | P }" := (@set_st _ (fun x => P))
 (at level 0, x name, P at level 200) : set_scope.
Notation "\set{ x : A | P }" := (@set_st A (fun x => P))
 (at level 0, x name, P at level 200) : set_scope.
Notation "\set{ x '\in' E | P }" := (@set_st _ (fun x => x \in E /\ P))
 (at level 0, x name, P at level 200) : set_scope.

Notation "\set{= e | x '\in' E }" :=
 (@set_st _ (fun a => exists_ x \in E, a = e ))
 (at level 0, x name, E at level 200) : set_scope.
Notation "\set{= e | x '\in' E , y ''\in' F }" :=
 (@set_st _ (fun a => exists_ x \in E, exists_ y \in F, a = e ))
 (at level 0, x name, F at level 200) : set_scope.
Notation "\set{= e | x y '\in' E }" :=
 (@set_st _ (fun a => exists_ x y \in E, a = e ))
 (at level 0, x name, y name, E at level 200) : set_scope.


(* ********************************************************************** *)
(** * Properties of sets *)

Section Instances.
Variables (A:Type).
Implicit Types E F : set A.

Transparent set finite empty_inst single_inst single_impl in_inst
  incl_inst inter_inst union_inst card_inst fold_inst remove_inst
  disjoint_inst.
Hint Constructors mem.

(** Local tactic to help unfolding all intermediate definitions *)

Ltac set_unf := unfold finite,
  card_inst, card_impl, card,
  to_list,
  disjoint_impl, disjoint_inst, disjoint,
  incl_inst, incl_impl,
  empty_inst, empty_impl, empty,
  single_inst, single_impl, single,
  in_inst, in_impl, is_in,
  incl_inst, incl_impl, incl,
  compl_impl, pred_not,
  inter_inst, inter_impl, inter, pred_and,
  union_inst, union_impl, union, pred_or,
  remove_inst, remove_impl, remove,
  fold_inst, fold_impl, fold in *.


(* ---------------------------------------------------------------------- *)
(** Reformulation *)

Lemma disjoint_eq_inter_empty : forall E F,
  (E \# F) = (E \n F = \{}).
Proof using. auto. Qed.


(* ---------------------------------------------------------------------- *)
(** set_st and double inclusion *)

Lemma in_set_st_eq : forall (P:A->Prop) x,
  x \in set_st P = P x.
Proof using. intros. apply* prop_ext. Qed.

Lemma set_ext_eq : forall E F,
  (E = F) = (forall (x:A), x \in E <-> x \in F).
Proof using.
  intros. apply prop_ext. iff H. subst*. extens*.
Qed.

Lemma set_ext : forall E F,
  (forall (x:A), x \in E <-> x \in F) ->
  E = F.
Proof using. intros. rewrite~ set_ext_eq. Qed.

Lemma set_st_eq : forall A (P Q : A -> Prop),
  (forall (x:A), P x <-> Q x) ->
  set_st P = set_st Q.
Proof using. intros. asserts_rewrite~ (P = Q). extens~. Qed.


(* ---------------------------------------------------------------------- *)
(** set_in, incl *)

Global Instance in_extens_inst : In_extens (A:=A) (T:=set A).
Proof using. constructor. intros. rewrite* set_ext_eq. Qed.

Global Instance in_empty_eq_inst : In_empty_eq (A:=A) (T:=set A).
Proof using. constructor. intros. apply* prop_ext. Qed.

Global Instance in_single_eq_inst : In_single_eq (A:=A) (T:=set A).
Proof using. constructor. intros. apply* prop_ext. Qed.

Global Instance in_union_eq_inst : In_union_eq (A:=A) (T:=set A).
Proof using. constructor. intros. set_unf. simpl. apply* prop_ext. Qed.

Global Instance in_inter_eq_inst : In_inter_eq (A:=A) (T:=set A).
Proof using. constructor. intros. set_unf. apply* prop_ext. Qed.

Global Instance in_remove_eq_inst : In_remove_eq (A:=A) (T:=set A).
Proof using. constructor. intros. set_unf. applys* prop_ext. Qed.

Global Instance incl_in_eq_inst : Incl_in_eq (A:=A) (T:=set A).
Proof using. constructor. intros. set_unf. autos*. Qed.

Global Instance disjoint_eq_inst : Disjoint_eq (T:=set A).
Proof using.
  constructor. intros. rewrite disjoint_eq_inter_empty.
  set_unf. applys prop_ext. iff M.
    intros x. rewrite* <- (@fun_eq_1 _ _ x _ _ M).
    extens*.
Qed.

(* -- LATER: fix naming conventions below *)

(* -- TODO
Lemma nonempty_eq_exists_one : forall E,
  finite E ->
  (E <> \{}) = (exists x, x \in E).
Proof using.
Qed.
*)

Lemma eq_union_single_remove_one : forall E x,
  x \in E ->
  E = \{x} \u (E \-- x).
Proof using.
  introv H. set_unf. extens. intros y. iff M.
    simpls. tests*: (y = x).
    destruct M. subst*. autos*.
Qed.

Lemma set_remove_one_add_same : forall E x,
  x \notin E ->
  E = (E \u \{x}) \-- x.
Proof using.
  introv Hx. set_unf. extens. iff.
  { split. eauto. intro. subst*. }
  { tauto. }
Qed.

(* ---------------------------------------------------------------------- *)
(** repr and covers *)

Lemma list_covers_of_list_repr : forall E L,
  list_repr E L ->
  list_covers E L.
Proof using. introv (ND&EQ). introv Hx. rewrite~ EQ. Qed.

Lemma list_repr_disjoint_union : forall E F LE LF,
  E \# F ->
  list_repr E LE ->
  list_repr F LF ->
  list_repr (E \u F) (LE ++ LF).
Proof using.
  introv D (HE&QE) (HF&QF). split.
  applys~ noduplicates_app.
    intros x ? ?. applys* @disjoint_inv x.
      typeclass. rewrite~ <- QE. rewrite~ <- QF.
    intros x. rewrite mem_app_eq. rewrite in_union_eq.
      rewrite <- QE. rewrite* <- QF.
Qed.

Lemma noduplicates_of_list_repr : forall E xs,
  list_repr E xs ->
  noduplicates xs.
Proof using. unfold list_repr. tauto. Qed.

(* see also [list_repr_nil] further on *)


(* ---------------------------------------------------------------------- *)
(** to_list *)

Lemma ex_list_repr_impl_of_ex_list_covers_impl : forall E,
  ex (list_covers_impl E) ->
  ex (list_repr_impl E).
Proof using.
  (* --TODO: factorize this wiht later proofs *)
  introv (L&M). sets_eq L1 EQL1: (remove_duplicates L).
  forwards~ (HN&HM&_): remove_duplicates_spec EQL1.
  sets L2: (filter (fun x => x \in E) L1).
  exists L2. split.
    applys* noduplicates_filter.
    intros x. specializes M x. rewrite <- HM in M. set_unf. iff N.
      subst L2. forwards*: mem_filter_inv N.
      applys* mem_filter.
Qed.

Lemma list_repr_to_list_of_finite : forall E,
  finite E ->
  list_repr E (to_list E).
Proof using.
  introv FE. unfolds to_list, finite, list_repr_impl.
  epsilon~ L'.
  applys~ ex_list_repr_impl_of_ex_list_covers_impl.
Qed.

(* corrolary of above, presented as an inversion lemma *)
Lemma eq_to_list_inv : forall E L,
  L = to_list E ->
  finite E ->
  list_repr E L.
Proof.
  introv EQ HE. unfolds. subst. forwards* (?&?): list_repr_to_list_of_finite HE.
Qed.

Lemma finite_eq_in_iff_mem_to_list : forall E,
  finite E = (forall x, x \in E <-> mem x (to_list E)).
Proof.
  intros. applys prop_ext. iff M.
  { forwards* (N1&N2): eq_to_list_inv E. intros x. specializes N2 x. autos*. }
  { exists (to_list E). intros x Ex. rewrite~ <- M. }
Qed.

Lemma to_list_empty :
  to_list (\{}:set A) = nil.
Proof using.
  set_unf. epsilon l.
  { exists (@nil A). split. { constructor. } { intros. rewrite* mem_nil_eq. } }
  intros Hl. inverts Hl. simpls. destruct~ l. false. rewrite <- H0. simple~.
Qed.

Lemma to_list_single : forall (x:A),
  to_list (\{x}) = x::nil.
Proof using.
  intros. unfold to_list. epsilon l.
  { exists (x::nil). split.
   { applys noduplicates_one. }
   { unfold single_inst, single_impl. simple~.
     intros. rewrite* mem_one_eq. } }
  introv Hl. unfolds single_inst, single_impl. simpls~.
  inverts Hl as H H0. destruct (H0 x). specializes~ H2.
  destruct l.
  { inverts H2. }
  { tests E: (x = a).
    { fequals. destruct l. auto. forwards~: (proj1 (H0 a0)).
      subst. inverts H as M1 M2. false* M1. }
    { inverts H2. false. forwards~: (proj1 (H0 a)). false. } }
Qed.

(* See also [finite_eq_mem_to_list] *)


(* ---------------------------------------------------------------------- *)
(** finite *)

(* introduction *)

Lemma finite_of_list_covers : forall (E:set A) L,
  list_covers E L ->
  finite E.
Proof using. introv H. exists* L. Qed.

Lemma finite_of_list_repr : forall (E:set A) L,
  list_repr E L ->
  finite E.
Proof using. introv (ND&EQ). exists~ L. introv Hx. rewrite~ EQ. Qed.

Lemma finite_of_ex_list_covers : forall (E:set A),
  ex (list_covers E) ->
  finite E.
Proof using. introv (L&H). applys* finite_of_list_covers. Qed.

(* elimination *)

Definition finite_inv_list_covers_and_card : forall (E:set A),
  finite E ->
  exists L, list_covers E L /\ card E = length L.
Proof.
  introv (L&H). sets m: (card E).
  forwards* (R&P): mmin_spec_nat m.
Qed.

Lemma finite_inv_list_covers : forall (E:set A),
  finite E ->
  exists L, list_covers E L.
Proof using. introv (L&HN). exists L. intros. applys* HN. Qed.

(* operations *)

Lemma finite_empty :
  finite (\{} : set A).
Proof using.
  intros. apply finite_of_ex_list_covers. set_unf.
  exists (@nil A). introv M. inverts M.
Qed.

Lemma finite_single : forall (a : A),
  finite \{a}.
Proof using.
  intros. apply finite_of_ex_list_covers. set_unf.
  exists (a::nil). introv M. hnf in M. subst*.
Qed.

Lemma finite_union : forall E F,
  finite E ->
  finite F ->
  finite (E \u F).
Proof using.
  introv H1 H2. apply finite_of_ex_list_covers.
  lets (L1&E1): finite_inv_list_covers H1.
  lets (L2&E2): finite_inv_list_covers H2.
  exists (L1++L2). unfolds list_covers.
  introv M.
  rewrite @in_union_eq in M; try typeclass.
  rewrite* mem_app_eq.
Qed.

Lemma finite_union_inv : forall E F,
  finite (E \u F) ->
  finite E /\ finite F.
Proof using.
  introv H. lets (L&HL): finite_inv_list_covers H. split.
  { apply finite_of_ex_list_covers. exists L.
    unfolds list_covers. intros x M. applys HL. apply in_union_l. auto. }
  { apply finite_of_ex_list_covers. exists L.
    unfolds list_covers. intros x M. applys HL. apply in_union_r. auto. }
Qed.

Lemma finite_union_eq : forall E F,
  finite (E \u F) = (finite E /\ finite F).
Proof using.
  extens. iff. applys* finite_union_inv. applys* finite_union.
Qed.

Lemma finite_inter : forall E F,
  finite E \/ finite F ->
  finite (E \n F).
Proof using.
  introv H. apply finite_of_ex_list_covers. destruct H.
  lets (L&EQ): finite_inv_list_covers H. exists L. unfold list_covers. set_unf. autos*.
  lets (L&EQ): finite_inv_list_covers H. exists L. unfold list_covers. set_unf. autos*.
Qed.

Lemma finite_inter_l : forall E F,
  finite E ->
  finite (E \n F).
Proof using. intros. applys* finite_inter. Qed.

Lemma finite_inter_r : forall E F,
  finite F ->
  finite (E \n F).
Proof using. intros. applys* finite_inter. Qed.

Lemma finite_incl : forall E F,
  E \c F ->
  finite F ->
  finite E.
Proof using.
  introv HI HF. apply finite_of_ex_list_covers.
  lets (L&EQ): finite_inv_list_covers HF. unfold list_covers.
  set_unf. exists* L. introv Ex. applys EQ. applys~ HI.
Qed.

Lemma finite_remove : forall E F,
  finite E ->
  finite (E \- F).
Proof using.
  introv HE. apply finite_of_ex_list_covers.
  lets (L&EQ): finite_inv_list_covers HE. unfold list_covers. set_unf. exists* L.
Qed.

Section Finite_remove_inv.
Local Opaque remove_inst single_inst.

Lemma finite_remove_inv : forall E F,
  finite (E \- F) ->
  finite F ->
  finite E.
Proof using.
  introv H1 H2. lets (L1&R1): finite_inv_list_covers H1.
  lets (L2&R2): finite_inv_list_covers H2.
  applys finite_of_list_covers (L1 ++ L2).
  intros y Hy. rewrite~ mem_app_eq. tests: (y \in F).
    autos~.
    forwards~ M: R1 y. rewrite~ @in_remove_eq. typeclass.
Qed.

End Finite_remove_inv.

Lemma finite_remove_one_inv : forall E x,
  finite (E \-- x) ->
  finite E.
Proof using.
  introv H. applys finite_remove_inv H. applys finite_single.
Qed.

(* --LATER : finite_remove_inv
   finite (E \- F) -> finite F -> finite E
*)

(* The following lemma pushed here due to dependencies. *)

Lemma list_repr_nil:
  list_repr \{} (@nil A).
Proof using.
  rewrite <- to_list_empty.
  eapply eq_to_list_inv; eauto using finite_empty.
Qed.


(* ---------------------------------------------------------------------- *)
(** card *)

(* introduction of properties on card *)

Definition list_covers_inv_card : forall (E:set A) L,
  list_covers E L ->
  (card E <= length L)%nat.
Proof using.
  introv H. sets m: (card E). set_unf.
  forwards* (R&P): mmin_spec_nat m.
  simpls. applys P. exists L. splits~.
Qed.

Definition finite_inv_list_repr_and_card : forall (E:set A),
  finite E ->
  exists L, list_repr E L /\ card E = length L.
Proof.
  introv H. forwards (L1&HL1&EL1): finite_inv_list_covers_and_card H.
  sets L2: (remove_duplicates L1).
  forwards~ (ND&EQ&LE): remove_duplicates_spec L1 L2.
  sets L3: (filter (fun x => x \in E) L2).
  asserts: (length L3 <= length L2)%nat. applys length_filter.
  asserts R3: (list_repr E L3).
    split.
      applys~ noduplicates_filter.
      intros x. iff M.
        unfold L3 in M. lets~ (_&?): mem_filter_inv M.
        applys~ mem_filter. rewrite~ EQ.
  forwards C3: list_covers_of_list_repr R3.
  exists L3. splits*.
  forwards: list_covers_inv_card C3. math.
Qed.

Lemma list_repr_inv_card : forall (E:set A) (L:list A),
  list_repr E L ->
  card E = length L.
Proof using.
  introv HR. lets (ND&EQ): HR.
  forwards~ (L'&(ND'&HR')&EQ'): finite_inv_list_repr_and_card E.
    applys* finite_of_list_repr.
  unfold card. simpl. rewrite EQ'.
  applys~ noduplicates_length_eq.
  intros x. rewrite EQ. rewrite* HR'.
Qed.

Definition finite_inv_card_ge : forall (E:set A) n,
  finite E ->
  (forall L, list_covers E L -> (length L >= n)%nat) ->
  (card E >= n)%nat.
Proof using.
  introv H. sets m: (card E).
  forwards* (R&P): mmin_spec_nat m.
    lets (L&EL): finite_inv_list_covers H. exists~ (length L) L.
  simpls. introv HL. destruct R as (L&CR&ER).
  forwards~: HL L. math.
Qed.

Definition list_covers_inv_card_eq : forall (E:set A) L,
  list_covers E L ->
  (forall L', list_covers E L' -> (length L' >= length L)%nat) ->
  card E = length L.
Proof using.
  introv HC HG.
  forwards~: list_covers_inv_card HC.
  forwards~: finite_inv_card_ge HG.
    applys* finite_of_list_covers.
  math.
Qed.

Lemma card_eq_length_to_list : forall (E:set A),
  finite E ->
  card E = length (to_list E).
Proof using.
  introv FE. applys list_repr_inv_card. applys~ eq_to_list_inv.
Qed.

(* operations *)

Global Instance card_empty_inst : Card_empty (T:=set A).
Proof using.
  constructor. rewrite card_eq_length_to_list.
  lets E: to_list_empty. set_unf. rewrite E. rew_list~.
  applys finite_empty.
Qed.

Global Instance card_single_inst : Card_single (T:=set A).
Proof using.
  constructor. intros a. rewrite card_eq_length_to_list.
  lets E: to_list_single a. set_unf. rewrite E. rew_list~.
  applys finite_single.
Qed.

End Instances.

#[global]
Hint Resolve finite_empty finite_single finite_union
  finite_inter finite_incl finite_remove : finite.


(* ********************************************************************** *)
(** * Tactics for proving set equalities and set inclusions *)

(** The tactic [set_prove] aims at proving set equality by testing
    double inclusion using a boolean tautology decision procedure. *)

(* lemmas *)

Section Autorewrite.
Variables (A : Type).
Implicit Types x y : A.
Implicit Types E F : set A.

Lemma set_in_empty_eq : forall x,
  x \in (\{}:set A) = False.
Proof using. apply in_empty_eq. Qed.

Lemma set_in_single_eq : forall x y,
  x \in (\{y}:set A) = (x = y).
Proof using. apply in_single_eq. Qed.

Lemma set_in_inter_eq : forall x E F,
  x \in (E \n F) = (x \in E /\ x \in F).
Proof using. apply in_inter_eq. Qed.

Lemma set_in_union_eq : forall x E F,
  x \in (E \u F) = (x \in E \/ x \in F).
Proof using. apply in_union_eq. Qed.

Lemma set_in_remove_eq : forall x E F,
  x \in (E \- F) = (x \in E /\ ~ x \in F).
Proof using. apply in_remove_eq. Qed.

Lemma set_in_extens_eq : forall E F,
  (E = F) = (forall x, x \in E <-> x \in F).
Proof using.
  extens. iff M.
  subst*.
  applys @in_extens_eq. typeclass. intros. extens*.
Qed.

Lemma set_incl_in_eq : forall E F,
  (E \c F) = (forall x, x \in E -> x \in F).
Proof using. apply incl_in_eq. Qed.

Lemma set_disjoint_eq : forall E F,
  (E \# F) = (forall x, x \in E -> x \in F -> False).
Proof using. apply disjoint_eq. Qed.

End Autorewrite.

#[global]
Hint Rewrite in_set_st_eq set_in_empty_eq set_in_single_eq
  set_in_inter_eq set_in_union_eq set_in_remove_eq set_in_extens_eq
  set_incl_in_eq set_disjoint_eq : rew_set.

(* tactic *)

Ltac rew_set_tactic tt :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_set).

Ltac set_specialize_hyps A x :=
  repeat match goal with H: forall _:?A, _ |- _ =>
    specializes H x
  end.

Ltac set_specialize_classic x :=
  repeat match goal with E: set _ |- _ =>
    match goal with
    | H: x \in E \/ ~ x \in E |- _ => fail 1
    | _ => lets: (prop_inv (x \in E))
    end
  end.

Ltac set_specialize use_classic :=
  match goal with |- forall _:?A, _ =>
    let x := fresh "x" in intros x;
    set_specialize_hyps A x;
    match use_classic with
    | true => set_specialize_classic x
    | false => idtac
    end
  end.

Ltac set_prove_setup use_classic :=
  intros;
  rew_set_tactic tt;
  try set_specialize use_classic;
  rew_set_tactic tt.

Ltac set_prove_conclude :=
  solve [ intros; subst; tauto ].

Ltac set_prove :=
  set_prove_setup false; set_prove_conclude.

Ltac set_prove_classic :=
  set_prove_setup true; set_prove_conclude.


(* ********************************************************************** *)
(** * More properties *)

(* ---------------------------------------------------------------------- *)
(** Card *)

Lemma card_le_of_incl : forall A (E F:set A),
  finite F ->
  E \c F ->
  (card E <= card F)%nat.
Proof using.
  introv FF CF. lets FE: finite_incl CF FF.
  lets (LF&RF&QF): finite_inv_list_covers_and_card FF.
  rewrite QF. applys list_covers_inv_card. introv Ex.
  applys RF. applys* @incl_inv. typeclass.
Qed.

Lemma card_union_le : forall A (E F:set A),
  finite E ->
  finite F ->
  card (E \u F) <= (card E + card F)%nat.
Proof using.
  introv FE FF.
  lets (LE&RE&QE): finite_inv_list_covers_and_card FE.
  lets (LF&RF&QF): finite_inv_list_covers_and_card FF.
  lets H: list_covers_inv_card (E \u F) (LE++LF) __.
    unfolds list_covers. intros. apply mem_app.
    rewrite in_union_eq in H. autos*.
  rew_list in H. math.
Qed.

Lemma card_disjoint_union : forall A (E F:set A),
  finite E ->
  finite F ->
  E \# F ->
  card (E \u F) = (card E + card F)%nat.
Proof using.
  introv FE FF EF.
  forwards: card_union_le FE FF.
  cuts: (card (E \u F) >= (card E + card F)%nat). math. clear H.
  forwards (L&LC&LL): finite_inv_list_covers_and_card (E \u F). applys~ finite_union.
  rewrite LL. clear LL.
  sets PE: (fun x => x \in E). sets LE: (filter PE L).
  sets PF: (fun x => x \in F). sets LF: (filter PF L).
  forwards: list_covers_inv_card E LE.
    unfold LE, PE. introv Ex. forwards: LC x. set_prove. applys~ mem_filter.
  forwards: list_covers_inv_card F LF.
    unfold LF, PF. introv Fx. forwards: LC x. set_prove. applys~ mem_filter.
  forwards LEF: filter_length_two_disjoint PE PF L.
    introv _ HEx HFx. unfolds PE, PF. applys* @disjoint_inv. typeclass.
  subst LE LF. math.
Qed.

Lemma card_inter_le_l : forall A (E F:set A),
  finite E ->
  card (E \n F) <= card E.
Proof using.
  intros. applys~ card_le_of_incl. set_prove.
Qed.

Lemma card_inter_le_r : forall A (E F:set A),
  finite F ->
  card (E \n F) <= card F.
Proof using.
  intros. rewrite inter_comm. apply~ card_inter_le_l.
Qed.

Lemma card_ge_one : forall A (E:set A) x,
  x \in E ->
  finite E ->
  1%nat <= card E.
Proof using.
  intros.
  rewrite <- (card_single x).
  applys~ card_le_of_incl.
  set_prove.
Qed.

(* -- LATER
Lemma card_nonempty : forall A (E:set A),
  E <> \{} ->
  finite E ->
  card E > 0.
Proof using.
Qed.
*)

Lemma card_disjoint_union_single : forall A (E:set A) x,
  finite E ->
  x \notin E ->
  (card (E \u \{x}) = card E + 1)%nat.
Proof using.
  intros.
  replace 1%nat with (card \{x}) by eauto using card_single.
  applys~ card_disjoint_union. applys finite_single.
  rewrite disjoint_single_r_eq. auto.
Qed.

Lemma card_diff_single : forall A (E:set A) x,
  finite E ->
  x \in E ->
  (card (E \-- x) = card E - 1)%nat.
Proof using.
  intros.
  assert (h1: (E \-- x) \u \{x} = E).
  { rewrite union_comm. erewrite eq_union_single_remove_one by eauto. reflexivity. }
  forwards h2: card_disjoint_union_single (E \-- x) x.
  { eauto with finite. }
  { unfold notin. rewrite set_in_remove_eq.
    rew_logic. right.
    eapply in_single_self. }
  rewrite h1 in h2.
  math.
Qed.


(* ---------------------------------------------------------------------- *)
(** fold *)

Lemma fold_eq_fold_to_list : forall A B (m:monoid_op B) (f:A->B) (E: set A),
  fold m f E = LibList.fold m f (to_list E).
Proof using. reflexivity. Qed.

Lemma fold_eq_fold_list_repr : forall A B (m:monoid_op B) (f:A->B) (E: set A) L,
  Comm_monoid m ->
  list_repr E L ->
  fold m f E = LibList.fold m f L.
Proof using.
  introv HM EL. rewrite fold_eq_fold_to_list.
  forwards~ (N&EQ2): eq_to_list_inv E. applys* finite_of_list_repr.
  destruct EL as (ND&EQ1).
  applys~ LibList.fold_equiv. intros. rewrite EQ2. rewrite* EQ1.
Qed.

Lemma fold_induction :
  forall A B (m : monoid_op B) (f : A -> B) (P : B -> Prop) (E : set A),
  Comm_monoid m ->
  P (monoid_neutral m) ->
  (forall x a, a \in E -> P x -> P (monoid_oper m (f a) x)) ->
  finite E ->
  P (fold m f E).
Proof using. (* --todo: cleanup proof *)
  introv Hm Hbase Hstep Hfinite.
  assert (forall xs, LibList.Forall (fun x => x \in E) xs -> P (LibList.fold m f xs)).
  { induction xs; rew_listx*. }
  forwards: list_repr_to_list_of_finite Hfinite.
  erewrite fold_eq_fold_list_repr by eauto.
  applys H. sets L: (to_list E). destruct H0 as (_&M).
  asserts M': (forall x : A, mem x L -> x \in E). { intros. applys* M. } clear M.
  { induction L. { constructor. } { constructor.
    { applys* M'. } { applys IHL. introv Lx. applys* M'. } } }
Qed.

Lemma fold_congruence : forall A B (m:monoid_op B) (f g:A -> B) (E:set A),
  Comm_monoid m ->
  finite E ->
  (forall x, x \in E -> f x = g x) ->
  fold m f E = fold m g E.
Proof using. (* --todo: cleanup proof *)
  introv Hm HE h. do 2 rewrite fold_eq_fold_to_list.
  eapply LibList.fold_congruence. intros.
  eapply h. rewrite finite_eq_in_iff_mem_to_list in HE. rewrite* HE.
Qed.

Lemma fold_empty : forall A B (m:monoid_op B) (f:A->B),
  fold m f (\{}:set A) = monoid_neutral m.
Proof using.
  intros. rewrite fold_eq_fold_to_list.
  rewrite to_list_empty. rewrite~ LibList.fold_nil.
Qed.

Lemma fold_single : forall A B (m:monoid_op B) (f:A->B) (x:A),
  Monoid m ->
  fold m f \{x} = f x.
Proof using.
  intros. rewrite fold_eq_fold_to_list.
  rewrite to_list_single. rewrite~ fold_cons.
  rewrite fold_nil. rewrite~ monoid_neutral_r.
Qed.

Lemma fold_union : forall A B (m:monoid_op B) (f:A->B) (E F:set A),
  Comm_monoid m ->
  finite E ->
  finite F ->
  E \# F ->
  fold m f (E \u F) = monoid_oper m (fold m f E) (fold m f F).
Proof using.
  introv HM HE HF HD.
  rewrites (>> fold_eq_fold_to_list E).
  rewrites (>> fold_eq_fold_to_list F).
  hint list_repr_to_list_of_finite.
  forwards~ HR: list_repr_disjoint_union HD.
  rewrites~ (>> fold_eq_fold_list_repr HR).
  rewrite~ LibList.fold_app. typeclass.
Qed.

Lemma fold_isolate : forall A (E:set A) x,
  finite E ->
  x \in E ->
  forall B (m : monoid_op B),
  Comm_monoid m ->
  forall (f : A -> B),
  fold m f E = monoid_oper m (f x) (fold m f (E \- \{x})).
Proof using. (* --todo: cleanup proof *)
  intros.
  (* Separate [E] into the singleton [\{x}] union the rest. *)
  rewrite (eq_union_single_remove_one E x) at 1 by eauto.
  (* Note that [f x] is the result of folding [f] over the singleton [\{x}]. *)
  erewrite <- (fold_single f x) by typeclass.
  (* Conclude. *)
  eapply fold_union; eauto using remove_disjoint with finite.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Structural properties *)

(** Rewriting tactics [rew_set] *)

#[global]
Hint Rewrite in_set_st_eq : rew_set.

Tactic Notation "rew_set" :=
  autorewrite with rew_set.
Tactic Notation "rew_set" "in" hyp(H) :=
  autorewrite with rew_set in H.
Tactic Notation "rew_set" "in" "*" :=
  autorewrite with rew_set in *.



(* ********************************************************************** *)
(** * MORE *)

(* ---------------------------------------------------------------------- *)
(** ** TEMPORARY Foreach *)

(** -- TODO: these lemmas should be instead derived as typeclasses
       in a generic way, in LibContainer. *)

(** -- TODO: add a paragraphe of the definition:
             foreach P E = (forall x, x \in E -> P x) *)

Section ForeachProp.
Variables (A : Type).
Implicit Types P Q : A -> Prop.
Implicit Types E F : set A.

Lemma foreach_empty : forall P,
  @foreach A (set A) _ P \{}.
Proof using. intros_all. false. Qed.
(* --TODO: false* @in_empty. typeclass. *)

Lemma foreach_single : forall P X,
  P X ->
  @foreach A (set A) _ P (\{ X }).
Proof using. intros_all. rewrite in_single_eq in H0. subst*. Qed.

Lemma foreach_union : forall P E F,
  foreach P E ->
  foreach P F ->
  foreach P (E \u F).
Proof using. intros_all. destruct~ (in_union_inv H1). Qed.

Lemma foreach_union_inv : forall P E F,
  foreach P (E \u F) ->
  foreach P E /\ foreach P F.
Proof using.
  introv H. split; introv K.
  apply H. rewrite~ @in_union_eq. typeclass.
  apply H. rewrite~ @in_union_eq. typeclass.
Qed.

Lemma foreach_union_eq : forall P E F,
  foreach P (E \u F) = (foreach P E /\ foreach P F).
Proof using.
  intros. extens. iff.
  apply~ foreach_union_inv.
  intuition eauto using foreach_union.
Qed.

Lemma foreach_single_eq : forall P X,
  foreach P (\{X}:set A) = P X.
Proof using.
  intros. extens. iff.
  apply H. apply in_single_self.
  apply~ foreach_single.
Qed.

Lemma foreach_of_pred_incl: forall P Q E,
  foreach P E ->
  pred_incl P Q ->
  foreach Q E.
Proof using. introv H L K. apply~ L. Qed.

Lemma foreach_remove_of_foreach_all : forall P E F,
  foreach P E ->
  foreach P (E \- F).
Proof using. introv M H. applys M. rewrite in_remove_eq in H. autos*. Qed.

Lemma foreach_remove : forall P E F,
  (forall x, x \in E -> x \notin F -> P x) ->
  foreach P (E \- F).
Proof using. introv M Px. rewrite in_remove_eq in Px. applys* M. Qed.

Lemma notin_of_foreach_not : forall P x E,
  foreach P E ->
  ~ P x ->
  x \notin E.
Proof using. introv M N I. applys N. applys~ M. Qed.

End ForeachProp.

#[global]
Hint Resolve foreach_empty foreach_single foreach_union.
#[global]
Hint Rewrite foreach_union_eq foreach_single_eq : rew_foreach.

Tactic Notation "rew_foreach" :=
  autorewrite with rew_foreach.
Tactic Notation "rew_foreach" "in" hyp(H) :=
  autorewrite with rew_foreach in H.
Tactic Notation "rew_foreach" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_foreach).
  (* autorewrite with rew_foreach in *.  *)
Tactic Notation "rew_foreach" "~" :=
  rew_foreach; auto_tilde.
Tactic Notation "rew_foreach" "*" :=
  rew_foreach; auto_star.
Tactic Notation "rew_foreach" "~" "in" constr(H) :=
  rew_foreach in H; auto_tilde.
Tactic Notation "rew_foreach" "*" "in" constr(H) :=
  rew_foreach in H; auto_star.
Tactic Notation "rew_foreach" "~" "in" "*" :=
  rew_foreach in *; auto_tilde.
Tactic Notation "rew_foreach" "*" "in" "*" :=
  rew_foreach in *; auto_star.


(* ---------------------------------------------------------------------- *)
(** FUTURE WORK *)

(* -- TODO

   map f E = \set{= f x | x in E }

   bij E F f g =
      forall x \in E, f x \in F
      forall y \in F, g x \in E
      forall x \in E, g (f x) = x
      forall y \in F, f (g y) = y

   F m i E = fold m j F
     when  bij E F f g
      and  forall x \in E,  i x = j (f x)
       or  forall y \in E,  j y = i (g y)
*)



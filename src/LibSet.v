(**************************************************************************
* TLC: A library for Coq                                                  *
* Sets                                                                    *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import Coq.Classes.Morphisms. (* for [Proper] instances *)
Require Import LibTactics LibLogic LibReflect LibList
  LibOperation LibStruct LibInt LibNat
  LibEpsilon LibRelation LibMin.
Require Export LibBag.


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
  @pred_not A. (* todo: as typeclass? *)

Definition union_impl : set A -> set A -> set A :=
  @pred_or A.

Definition inter_impl : set A -> set A -> set A :=
  @pred_and A.

Definition remove_impl : set A -> set A -> set A :=
  fun E F x => E x /\ ~ F x.

Definition incl_impl : set A -> set A -> Prop :=
  @pred_le A.

Definition disjoint_impl : set A -> set A -> Prop :=
  fun E F : set A => inter_impl E F = empty_impl.

Definition list_repr_impl (E:set A) (l:list A) :=
  No_duplicates l /\ forall x, Mem x l <-> E x.

Definition to_list (E:set A) :=
  epsilon (list_repr_impl E).

Definition to_set (xs : list A) : set A :=
  set_st (fun x => Mem x xs).

Definition list_covers_impl (E:set A) L :=
  forall x, E x -> Mem x L.

Definition finite (E:set A) :=
  exists L, list_covers_impl E L.

Definition card_impl (E:set A) : nat :=
  mmin le (fun n => exists L, list_covers_impl E L /\ n = length L).

Definition fold_impl (m:monoid_def B) (f:A->B) (E:set A) :=
  LibList.fold_right (fun x acc => monoid_oper m (f x) acc)
    (monoid_neutral m) (to_list E).

End Operations.


(* ---------------------------------------------------------------------- *)
(** ** Inhabited *)

Instance set_inhab : forall A, Inhab (set A).
Proof using. intros. apply (prove_Inhab (@empty_impl A)). Qed.


(* ---------------------------------------------------------------------- *)
(** ** Notation through typeclasses *)

Lemma in_inst : forall A, BagIn A (set A).
Proof using. constructor. exact (@in_impl A). Defined.
Hint Extern 1 (BagIn _ (set _)) => apply in_inst : typeclass_instances.
(* TODO: why is this not an instance like others ? *)

Instance empty_inst : forall A, BagEmpty (set A).
  constructor. apply (@empty_impl A). Defined.
Instance single_inst : forall A, BagSingle A (set A).
  constructor. rapply (@single_impl A). Defined.
Instance union_inst : forall A, BagUnion (set A).
  constructor. rapply (@union_impl A). Defined.
Instance inter_inst : forall A, BagInter (set A).
  constructor. rapply (@inter_impl A). Defined.
Instance remove_inst : forall A, BagRemove (set A) (set A).
  constructor. rapply (@remove_impl A). Defined.
Instance incl_inst : forall A, BagIncl (set A).
  constructor. rapply (@incl_impl A). Defined.
Instance disjoint_inst : forall A, BagDisjoint (set A).
  constructor. rapply (@disjoint_impl A). Defined.
Instance fold_inst : forall A B, BagFold B (A->B) (set A).
  constructor. rapply (@fold_impl A B). Defined.
Instance card_inst : forall A, BagCard (set A).
  constructor. rapply (@card_impl A). Defined.


Global Opaque set finite in_inst empty_inst single_inst union_inst inter_inst
  remove_inst incl_inst disjoint_inst card_inst fold_inst.



(* ---------------------------------------------------------------------- *)
(** Exposed definitions for list coverage *)

(* definitions *)

Definition list_repr A (E:set A) L :=
  No_duplicates L /\ forall x, Mem x L <-> x \in E.

Definition list_covers A (E:set A) L :=
  forall x, x \in E -> Mem x L.


(* ---------------------------------------------------------------------- *)
(** ** Notations for building sets *)

Notation "\set{ x | P }" := (@set_st _ (fun x => P))
 (at level 0, x ident, P at level 200) : set_scope.
Notation "\set{ x : A | P }" := (@set_st A (fun x => P))
 (at level 0, x ident, P at level 200) : set_scope.
Notation "\set{ x '\in' E | P }" := (@set_st _ (fun x => x \in E /\ P))
 (at level 0, x ident, P at level 200) : set_scope.

Notation "\set{= e | x '\in' E }" :=
 (@set_st _ (fun a => exists_ x \in E, a = e ))
 (at level 0, x ident, E at level 200) : set_scope.
Notation "\set{= e | x '\in' E , y ''\in' F }" :=
 (@set_st _ (fun a => exists_ x \in E, exists_ y \in F, a = e ))
 (at level 0, x ident, F at level 200) : set_scope.
Notation "\set{= e | x y '\in' E }" :=
 (@set_st _ (fun a => exists_ x y \in E, a = e ))
 (at level 0, x ident, y ident, E at level 200) : set_scope.


(* ---------------------------------------------------------------------- *)
(** Additional definitions *)

(* TODO

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

(* ********************************************************************** *)
(** * Properties of sets *)

Section Instances.
Variables (A:Type).
Transparent set finite empty_inst single_inst single_impl in_inst
  incl_inst inter_inst union_inst card_inst fold_inst remove_inst
  disjoint_inst.
Hint Constructors Mem.

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

Lemma disjoint_def : forall (E F : set A),
  E \# F = (E \n F = \{}).
Proof using. auto. Qed.

(* ---------------------------------------------------------------------- *)
(** set_st and double inclusion *)

Lemma in_set_st_eq : forall (P:A->Prop) x,
  x \in set_st P = P x.
Proof using. intros. apply* prop_ext. Qed.

Lemma set_ext_eq : forall (E F : set A),
  (E = F) = (forall (x:A), x \in E <-> x \in F).
Proof using.
  intros. apply prop_ext. iff H. subst*. apply* prop_ext_1.
Qed.

Lemma set_ext : forall (E F : set A),
  (forall (x:A), x \in E <-> x \in F) -> E = F.
Proof using. intros. rewrite~ set_ext_eq. Qed.

Lemma set_st_eq : forall A (P Q : A -> Prop),
  (forall (x:A), P x <-> Q x) -> set_st P = set_st Q.
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
  constructor. intros. rewrite disjoint_def.
  set_unf. applys prop_ext. iff M.
    intros x. rewrite* <- (@func_same_1 _ _ x _ _ M).
    applys* prop_ext_1.
Qed.

Lemma set_isolate : forall A (E : set A) x,
  x \in E ->
  E = \{x} \u (E \- \{x}).
Proof using.
  introv H. set_unf. apply prop_ext_1. intros y. iff M.
    simpls. tests*: (y = x).
    destruct M. subst*. autos*.
Qed.

Lemma set_add_remove : forall A (E : set A) x,
  x \notin E ->
  E = (E \u \{x}) \- \{x}.
Proof using.
  introv Hx. set_unf. apply prop_ext_1. iff.
  { split. eauto. intro. subst*. }
  { tauto. }
Qed.

(* ---------------------------------------------------------------------- *)
(** repr and covers *)

Lemma list_repr_covers : forall (E:set A) L,
  list_repr E L -> list_covers E L.
Proof using. introv (ND&EQ). introv Hx. rewrite~ EQ. Qed.

Lemma list_repr_disjoint_union : forall (E F : set A) LE LF,
  E \# F ->
  list_repr E LE ->
  list_repr F LF ->
  list_repr (E \u F) (LE ++ LF).
Proof using.
  introv D (HE&QE) (HF&QF). split.
  applys~ No_duplicates_app.
    intros x ? ?. applys* @disjoint_inv x.
      typeclass. rewrite~ <- QE. rewrite~ <- QF.
    intros x. rewrite Mem_app_or_eq. rewrite in_union_eq.
      rewrite <- QE. rewrite* <- QF.
Qed.

Lemma list_repr_no_duplicates:
  forall (E : set A) xs,
  list_repr E xs ->
  No_duplicates xs.
Proof using.
  unfold list_repr. tauto.
Qed.

(* see also [list_repr_nil] further on *)

(* ---------------------------------------------------------------------- *)
(** to_list *)

Lemma list_covers_impl_to_list_repr_impl : forall A (E:set A),
  ex (list_covers_impl E) -> ex (list_repr_impl E).
Proof using.
  (* TODO: factorize this wiht later proofs *)
  introv (L&M). sets_eq L1 EQL1: (Remove_duplicates L).
  forwards~ (HN&HM&_): Remove_duplicates_spec EQL1.
  sets L2: (Filter (fun x => x \in E) L1).
  exists L2. split.
    applys* No_duplicates_Filter.
    intros x. specializes M x. rewrite <- HM in M. set_unf. iff N.
      subst L2. forwards*: Filter_Mem_inv N.
      applys* Filter_Mem.
Qed.

Lemma finite_list_repr : forall A (E:set A),
  finite E -> list_repr E (to_list E).
Proof using.
  introv FE. unfolds to_list, finite, list_repr_impl.
  spec_epsilon~ as L' (HL'&EL').
  applys~ list_covers_impl_to_list_repr_impl. splits~.
Qed.

Lemma to_list_spec : forall (E:set A) L,
  L = to_list E -> finite E -> list_repr E L.
Proof.
  introv EQ HE. unfolds. subst. forwards* (?&?): finite_list_repr HE.
Qed.

Lemma Mem_to_list:
  forall (xs : set A),
  finite xs ->
  forall x,
  Mem x (to_list xs) <-> x \in xs.
Proof.
  intros. forwards [ ? ? ]: to_list_spec xs; eauto.
Qed.

Lemma to_list_empty :
  to_list (\{}:set A) = nil.
Proof using.
  set_unf. spec_epsilon as l.
  exists (@nil A). split. constructor. iff; false_invert.
  inverts Hl. simpls. destruct~ l. false. rewrite <- H0. simple~.
Qed.

Lemma to_list_single : forall (x:A),
  to_list (\{x}) = x::nil.
Proof using.
  intros. unfold to_list. spec_epsilon as l.
    exists (x::nil). split.
      constructor*. introv M. inverts M.
      unfold single_inst, single_impl. simple~.
       iff H. inverts* H. inverts* H1. subst*.
  unfolds single_inst, single_impl. simpls~.
  inverts Hl as H H0. destruct (H0 x). specializes~ H2.
  destruct l.
    inverts H2.
    tests E: (x = a).
      fequals. destruct l. auto. forwards~: (proj1 (H0 a0)).
       subst. inverts H as M1 M2. false* M1.
      inverts H2. false. forwards~: (proj1 (H0 a)). false.
Qed.

(* ---------------------------------------------------------------------- *)
(** finite *)

(* introduction *)

Lemma finite_prove_covers : forall (E:set A) L,
  list_covers E L -> finite E.
Proof using. introv H. exists* L. Qed.

Lemma finite_prove_repr : forall (E:set A) L,
  list_repr E L -> finite E.
Proof using. introv (ND&EQ). exists~ L. introv Hx. rewrite~ EQ. Qed.

Lemma finite_prove_exists : forall (E:set A),
  ex (list_covers E) -> finite E.
Proof using. introv (L&H). applys* finite_prove_covers. Qed.

(* elimination *)

Definition finite_covers : forall (E:set A),
  finite E -> exists L, list_covers E L /\ card E = length L.
Proof.
  introv (L&H). sets m: (card E).
  forwards* (R&P): mmin_spec_nat m.
Qed.

Lemma finite_covers_basic : forall (E:set A),
  finite E -> exists L, list_covers E L.
Proof using. introv (L&HN). exists L. intros. applys* HN. Qed.

(* operations *)

Lemma finite_empty :
  finite (\{} : set A).
Proof using.
  intros. apply finite_prove_exists. set_unf.
  exists (@nil A). introv M. inverts M.
Qed.

Lemma finite_single : forall (a : A),
  finite \{a}.
Proof using.
  intros. apply finite_prove_exists. set_unf.
  exists (a::nil). introv M. hnf in M. subst*.
Qed.

Lemma finite_union : forall (E F : set A),
  finite E ->
  finite F ->
  finite (E \u F).
Proof using.
  introv H1 H2. apply finite_prove_exists.
  lets (L1&E1): finite_covers_basic H1.
  lets (L2&E2): finite_covers_basic H2.
  exists (L1++L2). unfolds list_covers.
  introv M.
  rewrite @in_union_eq in M; try typeclass.
  rewrite* Mem_app_or_eq.
Qed.

Lemma finite_inter : forall (E F : set A),
  finite E \/ finite F ->
  finite (E \n F).
Proof using.
  introv H. apply finite_prove_exists. destruct H.
  lets (L&EQ): finite_covers_basic H. exists L. unfold list_covers. set_unf. autos*.
  lets (L&EQ): finite_covers_basic H. exists L. unfold list_covers. set_unf. autos*.
Qed.

Lemma finite_incl : forall (E F : set A),
  E \c F ->
  finite F ->
  finite E.
Proof using.
  introv HI HF. apply finite_prove_exists.
  lets (L&EQ): finite_covers_basic HF. unfold list_covers.
  set_unf. exists* L. introv Ex. applys EQ. applys~ HI.
Qed.

Lemma finite_remove : forall (E F : set A),
  finite E ->
  finite (E \- F).
Proof using.
  introv HE. apply finite_prove_exists.
  lets (L&EQ): finite_covers_basic HE. unfold list_covers. set_unf. exists* L.
Qed.

Section One.
Lemma finite_remove_inv : forall (E F : set A),
  finite (E \- F) -> finite F -> finite E.
Proof using.
  Local Opaque remove_inst single_inst.
  introv H1 H2. lets (L1&R1): finite_covers_basic H1.
  lets (L2&R2): finite_covers_basic H2.
  applys finite_prove_covers (L1 ++ L2).
  intros y Hy. rewrite~ Mem_app_or_eq. tests: (y \in F).
    autos~.
    forwards~ M: R1 y. rewrite~ @in_remove_eq. typeclass.
Qed.
End One.

Lemma finite_remove_one_inv : forall (E : set A) x,
  finite (E \-- x) -> finite E.
Proof using.
  introv H. applys finite_remove_inv H. applys finite_single.
Qed.

(* LATER : finite_remove_inv
   finite (E \- F) -> finite F -> finite E
*)

(* The following lemma pushed here due to dependencies. *)

Lemma list_repr_nil:
  list_repr \{} (@nil A).
Proof using.
  rewrite <- to_list_empty.
  eapply to_list_spec; eauto using finite_empty.
Qed.

(* ---------------------------------------------------------------------- *)
(** card *)

(* introduction of properties on card *)

Definition card_prove_le : forall (E:set A) L,
  list_covers E L -> (card E <= length L)%nat.
Proof using.
  introv H. sets m: (card E). set_unf.
  forwards* (R&P): mmin_spec_nat m.
  simpls. applys P. exists L. splits~.
Qed.

Definition finite_repr_length : forall (E:set A),
  finite E -> exists L, list_repr E L /\ card E = length L.
Proof.
  introv H. forwards (L1&HL1&EL1): finite_covers H.
  sets L2: (Remove_duplicates L1).
  forwards~ (ND&EQ&LE): Remove_duplicates_spec L1 L2.
  sets L3: (Filter (fun x => x \in E) L2).
  asserts: (length L3 <= length L2)%nat. applys Filter_length_le.
  asserts R3: (list_repr E L3).
    split.
      applys~ No_duplicates_Filter.
      intros x. iff M.
        unfold L3 in M. lets~ (_&?): Filter_Mem_inv M.
        applys~ Filter_Mem. rewrite~ EQ.
  forwards C3: list_repr_covers R3.
  exists L3. splits*.
  forwards: card_prove_le C3. math.
Qed.

Lemma list_repr_card : forall (E:set A) (L:list A),
  list_repr E L -> card E = length L.
Proof using.
  introv HR. lets (ND&EQ): HR.
  forwards~ (L'&(ND'&HR')&EQ'): finite_repr_length E.
    applys* finite_prove_repr.
  unfold card. simpl. rewrite EQ'.
  applys~ No_duplicates_length_eq.
  intros x. rewrite EQ. rewrite* HR'.
Qed.

Definition card_prove_ge : forall (E:set A) n,
  finite E -> (forall L, list_covers E L -> (length L >= n)%nat) ->
  (card E >= n)%nat.
Proof using.
  introv H. sets m: (card E).
  forwards* (R&P): mmin_spec_nat m.
    lets (L&EL): finite_covers_basic H. exists~ (length L) L.
  simpls. introv HL. destruct R as (L&CR&ER).
  forwards~: HL L. math.
Qed.

Definition card_prove_eq : forall (E:set A) L,
  list_covers E L ->
  (forall L', list_covers E L' -> (length L' >= length L)%nat) ->
  card E = length L.
Proof using.
  introv HC HG.
  forwards~: card_prove_le HC.
  forwards~: card_prove_ge HG. applys* finite_prove_covers.
  math.
Qed.

Lemma card_is_length_to_list : forall (E:set A),
  finite E -> card E = length (to_list E).
Proof using.
  introv FE. applys list_repr_card. applys~ to_list_spec.
Qed.

(* operations *)

Global Instance card_empty_inst : Card_empty (T:=set A).
Proof using.
  constructor. rewrite card_is_length_to_list.
  lets E: to_list_empty. set_unf. rewrite E. rew_list~.
  applys finite_empty.
Qed.

Global Instance card_single_inst : Card_single (T:=set A).
Proof using.
  constructor. intros a. rewrite card_is_length_to_list.
  lets E: to_list_single a. set_unf. rewrite E. rew_list~.
  applys finite_single.
Qed.


End Instances.

Hint Resolve finite_empty finite_single finite_union
  finite_inter finite_incl finite_remove : finite.

(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)
(* ** Tactics for proving set equalities and set inclusions *)

(* lemmas *)

Section Autorewrite.
Variables (A : Type).
Implicit Types x y : A.
Implicit Types E F : set A.

Lemma set_in_empty_eq : forall x, x \in (\{}:set A) = False.
Proof using.
  apply in_empty_eq.
Qed.

Lemma set_in_single_eq : forall x y, x \in (\{y}:set A) = (x = y).
Proof using.
  apply in_single_eq.
Qed.

Lemma set_in_inter_eq : forall x E F, x \in (E \n F) = (x \in E /\ x \in F).
Proof using.
  apply in_inter_eq.
Qed.

Lemma set_in_union_eq : forall x E F, x \in (E \u F) = (x \in E \/ x \in F).
Proof using.
  apply in_union_eq.
Qed.

Lemma set_in_remove_eq : forall x E F, x \in (E \- F) = (x \in E /\ ~ x \in F).
Proof using.
  apply in_remove_eq.
Qed.

Lemma set_in_extens_eq : forall E F, (E = F) = (forall x, x \in E <-> x \in F).
Proof using.
  extens. iff M.
  subst*.
  applys @in_extens_eq. typeclass. intros. extens*.
Qed.

Lemma set_incl_in_eq : forall E F, (E \c F) = (forall x, x \in E -> x \in F).
Proof using.
  apply incl_in_eq.
Qed.

Lemma set_disjoint_eq : forall E F, (E \# F) = (forall x, x \in E -> x \in F -> False).
Proof using.
  apply disjoint_eq.
Qed.

End Autorewrite.

Hint Rewrite in_set_st_eq set_in_empty_eq set_in_single_eq set_in_inter_eq set_in_union_eq
  set_in_remove_eq set_in_extens_eq set_incl_in_eq set_disjoint_eq : set_norm.


(* tactics *)

Ltac set_norm :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with set_norm).

Ltac set_specialize_hyps A x :=
  repeat match goal with H: forall _:?A, _ |- _ =>
    specializes H x
  end.

Ltac set_specialize_classic x :=
  repeat match goal with E: set _ |- _ =>
    match goal with
    | H: x \in E \/ ~ x \in E |- _ => fail 1
    | _ => lets: (classic (x \in E))
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
  set_norm;
  try set_specialize use_classic;
  set_norm.

Ltac set_prove_conclude :=
  solve [ intros; subst; tauto ].

Ltac set_prove :=
  set_prove_setup false; set_prove_conclude.

Ltac set_prove_classic :=
  set_prove_setup true; set_prove_conclude.

(* demos *)

Lemma inter_union_disjoint_right:
  forall A (E F G : set A),
  F \# G ->
  (E \u F) \n G = (E \n G).
Proof using.
  set_prove.
  (* intros. set_norm. set_specialize. set_norm. tauto. *)
Qed. (* demo *)

Lemma inter_union_subset_right:
  forall A (E F G : set A),
  F \c G ->
  (E \u F) \n G = (E \n G) \u F.
Proof using.
  set_prove.
Qed. (* demo *)

Lemma inter_covariant:
  forall A (E E' F F' : set A),
  E \c E' ->
  F \c F' ->
  (E \n F) \c (E' \n F').
Proof using.
  set_prove.
Qed. (* demo *)

Lemma set_decompose_inter_right :
  forall A (E F : set A),
  E = (E \n F) \u (E \- F).
Proof using.
  set_prove_classic.
Qed. (* demo *)

Lemma set_decompose_union_right :
  forall A (E F : set A),
  (E \u F) = E \u (F \- E).
Proof using.
  set_prove_classic.
Qed. (* demo *)



(* ---------------------------------------------------------------------- *)
(** card *)

Lemma card_incl_le : forall A (E F:set A),
  finite F ->
  E \c F ->
  (card E <= card F)%nat.
Proof using.
  introv FF CF. lets FE: finite_incl CF FF.
  lets (LF&RF&QF): finite_covers FF.
  rewrite QF. applys card_prove_le. introv Ex.
  applys RF. applys* @incl_inv. typeclass.
Qed.

Lemma card_union_le : forall A (E F:set A),
  finite E -> finite F ->
  card (E \u F) <= (card E + card F)%nat.
Proof using.
  introv FE FF.
  lets (LE&RE&QE): finite_covers FE.
  lets (LF&RF&QF): finite_covers FF.
  lets H: card_prove_le (E \u F) (LE++LF) __.
    unfolds list_covers. intros. apply Mem_app_or.
    rewrite in_union_eq in H. autos*.
  rew_length in H. math.
Qed.

Lemma card_disjoint_union : forall A (E F : set A),
  finite E ->
  finite F ->
  E \# F ->
  card (E \u F) = (card E + card F)%nat.
Proof using.
  introv FE FF EF.
  forwards: card_union_le FE FF.
  cuts: (card (E \u F) >= (card E + card F)%nat). math. clear H.
  forwards (L&LC&LL): finite_covers (E \u F). applys~ finite_union.
  rewrite LL. clear LL.
  sets PE: (fun x => x \in E). sets LE: (Filter PE L).
  sets PF: (fun x => x \in F). sets LF: (Filter PF L).
  forwards: card_prove_le E LE.
    unfold LE, PE. introv Ex. forwards: LC x. set_prove. applys~ Filter_Mem.
  forwards: card_prove_le F LF.
    unfold LF, PF. introv Fx. forwards: LC x. set_prove. applys~ Filter_Mem.
  forwards LEF: Filter_disjoint_predicates_length PE PF L.
    introv _ HEx HFx. unfolds PE, PF. applys* @disjoint_inv. typeclass.
  subst LE LF. math.
Qed.

Lemma card_inter_left : forall A (E F : set A),
  finite E ->
  card (E \n F) <= card E.
Proof using.
  intros. applys~ card_incl_le. set_prove.
Qed.

Lemma card_inter_right : forall A (E F : set A),
  finite F ->
  card (E \n F) <= card F.
Proof using.
  intros. rewrite inter_comm. apply~ card_inter_left.
Qed.

Lemma card_nonempty : forall A (E : set A) x,
  x \in E ->
  finite E ->
  1 <= card E.
Proof using.
  intros.
  rewrite <- (card_single x).
  applys~ card_incl_le.
  set_prove.
Qed.

Lemma card_disjoint_union_single : forall A (E : set A) x,
  finite E ->
  x \notin E ->
  (card (E \u \{x}) = card E + 1)%nat.
Proof using.
  intros.
  replace 1 with (card \{x}) by eauto using card_single.
  applys~ card_disjoint_union. applys finite_single.
  rewrite disjoint_single_r_eq. auto.
Qed.

Lemma card_diff_single:
  forall A (E : set A) x,
  finite E ->
  x \in E ->
  (card (E \-- x) = card E - 1)%nat.
Proof using.
  intros.
  assert (h1: (E \-- x) \u \{x} = E).
  { rewrite union_comm. erewrite set_isolate by eauto. reflexivity. }
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

Lemma fold_def : forall A B (m:monoid_def B) (f:A->B) (E: set A),
  fold m f E = LibList.fold m f (to_list E).
Proof using. reflexivity. Qed.

Lemma fold_eq : forall A B (m:monoid_def B) (f:A->B) (E: set A) L,
  Monoid_commutative m ->
  list_repr E L ->
  fold m f E = LibList.fold m f L.
Proof using.
  introv HM EL. rewrite fold_def.
  forwards~ (N&EQ2): to_list_spec E. applys* finite_prove_repr.
  destruct EL as (ND&EQ1).
  applys~ LibList.fold_equiv. intros. rewrite EQ2. rewrite* EQ1.
Qed.

Lemma fold_induction:
  forall A B (m : monoid_def B) (f : A -> B) (P : B -> Prop),
  Monoid_commutative m ->
  P (monoid_neutral m) ->
  (forall x a, P x -> P (monoid_oper m (f a) x)) ->
  forall E,
  finite E ->
  P (fold m f E).
Proof using.
  introv ? Hbase Hstep Hfinite.
  assert (forall xs, P (LibList.fold m f xs)).
  { induction xs; unfold LibList.fold; simpl; eauto. }
  forwards: finite_list_repr Hfinite.
  erewrite fold_eq by eauto.
  eauto.
Qed.

Lemma fold_congruence : forall A B (m : monoid_def B) (f g : A -> B) (E : set A),
  Monoid_commutative m ->
  finite E ->
  (forall x, x \in E -> f x = g x) ->
  fold m f E = fold m g E.
Proof using.
  introv ? ? h. do 2 rewrite fold_def.
  eapply LibList.fold_congruence. intros.
  eapply h. eapply Mem_to_list; eauto.
Qed.

Lemma fold_empty : forall A B (m:monoid_def B) (f:A->B),
  fold m f (\{}:set A) = monoid_neutral m.
Proof using.
  intros. rewrite fold_def.
  rewrite to_list_empty. rewrite~ LibList.fold_nil.
Qed.

Lemma fold_single : forall A B (m:monoid_def B) (f:A->B) (x:A),
  Monoid m ->
  fold m f \{x} = f x.
Proof using.
  intros. rewrite fold_def.
  rewrite to_list_single. rewrite~ fold_cons.
  rewrite fold_nil. rewrite~ monoid_neutral_r.
Qed.

Lemma fold_union : forall A B (m:monoid_def B) (f:A->B) (E F : set A),
  Monoid_commutative m ->
  finite E ->
  finite F ->
  E \# F ->
  fold m f (E \u F) = monoid_oper m (fold m f E) (fold m f F).
Proof using.
  introv HM HE HF HD.
  rewrites (>> fold_def E).
  rewrites (>> fold_def F).
  hint finite_list_repr. forwards~ HR: list_repr_disjoint_union HD.
  rewrites~ (>> fold_eq HR).
  rewrite~ LibList.fold_app. typeclass.
Qed.

Lemma fold_isolate :
  forall A (E : set A) x,
  finite E ->
  x \in E ->
  forall B (m : monoid_def B),
  Monoid_commutative m ->
  forall (f : A -> B),
  fold m f E = monoid_oper m (f x) (fold m f (E \- \{x})).
Proof using.
  intros.
  (* Separate [E] into the singleton [\{x}] union the rest. *)
  rewrite (set_isolate E x) at 1 by eauto.
  (* Note that [f x] is the result of folding [f] over the singleton [\{x}]. *)
  erewrite <- (fold_single f x) by typeclass.
  (* Conclude. *)
  eapply fold_union; eauto using remove_disjoint with finite.
Qed.

Lemma fold_pointwise:
  forall B (m : monoid_def B) (leB : B -> B -> Prop),
  Monoid m ->
  refl leB ->
  Proper (leB ++> leB ++> leB) (monoid_oper m) ->
  forall A (E : set A),
  finite E ->
  forall (f f' : A -> B),
  (forall x, x \in E -> leB (f x) (f' x)) ->
  leB (fold m f E) (fold m f' E).
Proof using.
  intros. do 2 rewrite fold_def.
  applys~ LibList.fold_pointwise.
  intros x. forwards~ (_&EQ): finite_list_repr E. rewrite (EQ x). auto.
Qed.

(* ---------------------------------------------------------------------- *)
(** [to_set] *)

Lemma list_repr_to_set:
  forall A (xs : list A),
  No_duplicates xs ->
  list_repr (to_set xs) xs.
Proof using.
  unfold list_repr, to_set. induction 1; split.
  { econstructor. }
  { tauto. }
  { econstructor; eauto. }
  { tauto. }
Qed.

Lemma list_repr_to_set_inverse:
  forall A (E : set A) (xs : list A),
  list_repr E xs ->
  E = to_set xs.
Proof using.
  unfold list_repr, to_set. introv (_ & ?).
  generalize dependent E. generalize dependent xs.
  induction xs; introv H; rewrite set_ext_eq; intros x;
  rewrite in_set_st_eq; rewrite H; tauto.
Qed.

Lemma to_set_nil:
  forall A,
  to_set (@nil A) = \{}.
Proof using.
  intros.
  erewrite <- list_repr_to_set_inverse by eapply list_repr_nil.
  eauto.
Qed.

Lemma prefix_to_set:
  forall A (xs ys : list A),
  prefix xs ys ->
  to_set xs \c to_set ys.
Proof using.
  unfold to_set. introv (zs&?). subst.
  rewrite set_incl_in_eq. intros. rewrite in_set_st_eq in *.
  rewrite Mem_app_or_eq. tauto.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Structural properties *)

(** Rewriting tactics *)

Hint Rewrite in_set_st_eq : rew_set.
Tactic Notation "rew_set" :=
  autorewrite with rew_set.
Tactic Notation "rew_set" "in" hyp(H) :=
  autorewrite with rew_set in H.
Tactic Notation "rew_set" "in" "*" :=
  autorewrite with rew_set in *.



(* ********************************************************************** *)
(** * Additional predicates on sets *)

(* ---------------------------------------------------------------------- *)
(** ** Foreach *)

(** TODO: derive these lemmas as typeclasses in a generic way in LibBag *)

Section ForeachProp.
Variables (A : Type).
Implicit Types P Q : A -> Prop.
Implicit Types E F : set A.

Lemma foreach_empty : forall P,
  @foreach A (set A) _ P \{}.
Proof using. intros_all. false. Qed.
(* TODO: false* @in_empty. typeclass. *)

Lemma foreach_single : forall P X,
  P X -> @foreach A (set A) _ P (\{ X }).
Proof using. intros_all. rewrite in_single_eq in H0. subst*. Qed.

Lemma foreach_union : forall P E F,
  foreach P E -> foreach P F -> foreach P (E \u F).
Proof using. intros_all. destruct~ (in_union_inv H1). Qed.

Lemma foreach_union_inv : forall P E F,
  foreach P (E \u F) -> foreach P E /\ foreach P F.
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

Lemma foreach_weaken : forall P Q E,
  foreach P E -> pred_le P Q -> foreach Q E.
Proof using. introv H L K. apply~ L. Qed.

Lemma foreach_remove_simple : forall P E F,
  foreach P E -> foreach P (E \- F).
Proof using. introv M H. applys M. rewrite in_remove_eq in H. autos*. Qed.

Lemma foreach_remove : forall P Q E F,
  foreach P E -> pred_le P (fun (x:A) => x \notin F -> Q x) -> foreach Q (E \- F).
Proof using. introv M H Px. rewrite in_remove_eq in Px. applys* H. Qed.

Lemma foreach_notin_prove : forall P x E,
  foreach P E -> ~ P x -> x \notin E.
Proof using. introv M N I. applys N. applys~ M. Qed.

End ForeachProp.

Hint Resolve foreach_empty foreach_single foreach_union.
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


(* ********************************************************************** *)
(** * Tactics *)

(* DEPRECATED, use "set_prove" when possible *)

(* ---------------------------------------------------------------------- *)
(** ** Tactics to prove equalities on unions *)

(* Documentation appears further on *)

Lemma for_set_union_assoc : forall A, assoc (union (T:=set A)).
Proof using. intros. apply union_assoc. Qed.

Lemma for_set_union_comm : forall A, comm (union (T:=set A)).
Proof using. intros. apply union_comm. Qed.

Lemma for_set_union_empty_l : forall A (E:set A), \{} \u E = E.
Proof using. intros. apply union_empty_l. Qed.

Lemma for_set_union_empty_r : forall A (E:set A), E \u \{} = E.
Proof using. intros. apply union_empty_r. Qed.

Hint Rewrite <- for_set_union_assoc : rew_permut_simpl.
Hint Rewrite for_set_union_empty_l for_set_union_empty_r : rew_permut_simpl.
Ltac rew_permut_simpl :=
  autorewrite with rew_permut_simpl; try typeclass.
Ltac rews_permut_simpl :=
  autorewrite with rew_permut_simpl in *; try typeclass.

Section PermutationTactic.
Context (A:Type).
Implicit Types l : set A.

Lemma permut_get_1 : forall l1 l2,
  (l1 \u l2) = (l1 \u l2).
Proof using. intros. auto. Qed.

Lemma permut_get_2 : forall l1 l2 l3,
  (l1 \u l2 \u l3) = (l2 \u l1 \u l3).
Proof using. intros. apply union_comm_assoc. Qed.

Lemma permut_get_3 : forall l1 l2 l3 l4,
  (l1 \u l2 \u l3 \u l4) = (l2 \u l3 \u l1 \u l4).
Proof using.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_2.
Qed.

Lemma permut_get_4 : forall l1 l2 l3 l4 l5,
    (l1 \u l2 \u l3 \u l4 \u l5)
  = (l2 \u l3 \u l4 \u l1 \u l5).
Proof using.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_3.
Qed.

Lemma permut_get_5 : forall l1 l2 l3 l4 l5 l6,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l6)
  = (l2 \u l3 \u l4 \u l5 \u l1 \u l6).
Proof using.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_4.
Qed.

Lemma permut_get_6 : forall l1 l2 l3 l4 l5 l6 l7,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l6 \u l7)
  = (l2 \u l3 \u l4 \u l5 \u l6 \u l1 \u l7).
Proof using.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_5.
Qed.

Lemma permut_get_7 : forall l1 l2 l3 l4 l5 l6 l7 l8,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l6 \u l7 \u l8)
  = (l2 \u l3 \u l4 \u l5 \u l6 \u l7 \u l1 \u l8).
Proof using.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_6.
Qed.

Lemma permut_get_8 : forall l1 l2 l3 l4 l5 l6 l7 l8 l9,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l6 \u l7 \u l8 \u l9)
  = (l2 \u l3 \u l4 \u l5 \u l6 \u l7 \u l8 \u l1 \u l9).
Proof using.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_7.
Qed.

Lemma permut_cancel_1 : forall l1 l2,
  (l1 \u l1 \u l2) = l1 \u l2.
Proof using. intros. rewrite union_assoc. rewrite union_self. auto. Qed.

Lemma permut_cancel_2 : forall l1 l2 l3,
  (l1 \u l2 \u l1 \u l3) = (l1 \u l2 \u l3).
Proof using.
  intros. rewrite <- (@permut_get_2 l1). apply permut_cancel_1.
Qed.

Lemma permut_cancel_3 : forall l1 l2 l3 l4,
  (l1 \u l2 \u l3 \u l1 \u l4) = (l1 \u l2 \u l3 \u l4).
Proof using.
  intros. rewrite <- (@permut_get_3 l1). apply permut_cancel_1.
Qed.

Lemma permut_cancel_4 : forall l1 l2 l3 l4 l5,
    (l1 \u l2 \u l3 \u l4 \u l1 \u l5)
  = (l1 \u l2 \u l3 \u l4 \u l5).
Proof using.
  intros. rewrite <- (@permut_get_4 l1). apply permut_cancel_1.
Qed.

Lemma permut_cancel_5 : forall l1 l2 l3 l4 l5 l6,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l1 \u l6)
  = (l1 \u l2 \u l3 \u l4 \u l5 \u l6).
Proof using.
  intros. rewrite <- (@permut_get_5 l1). apply permut_cancel_1.
Qed.

Lemma permut_tactic_setup : forall l1 l2,
   (\{} \u l1 \u \{}) = (l2 \u \{}) -> l1 = l2.
Proof using. intros. rews_permut_simpl. Qed.

Lemma permut_tactic_keep : forall l1 l2 l3 l4,
  ((l1 \u l2) \u l3) = l4 ->
  (l1 \u (l2 \u l3)) = l4.
Proof using. intros. rews_permut_simpl. Qed.

Lemma permut_tactic_simpl : forall l1 l2 l3 l4,
  (l1 \u l3) = l4 ->
  (l1 \u (l2 \u l3)) = (l2 \u l4).
Proof using. intros. subst. apply permut_get_2. Qed.

Lemma permut_tactic_trans : forall l1 l2 l3,
  l3 = l2 -> l1 = l3 -> l1 = l2.
Proof using. intros. subst~. Qed.

End PermutationTactic.

(** [permut_lemma_get n] returns the lemma [permut_get_n]
    for the given value of [n] *)

Ltac permut_lemma_get n :=
  match nat_from_number n with
  | 1%nat => constr:(permut_get_1)
  | 2%nat => constr:(permut_get_2)
  | 3%nat => constr:(permut_get_3)
  | 4%nat => constr:(permut_get_4)
  | 5%nat => constr:(permut_get_5)
  end.

(** [permut_prepare] applies to a goal of the form [permut l l']
    and sets [l] and [l'] in the form [l1 \u l2 \u .. \u \{}],
    (some of the lists [li] are put in the form [x::\{}]). *)

Ltac permut_simpl_prepare :=
   rew_permut_simpl;
   apply permut_tactic_setup;
   repeat rewrite <- union_assoc.

(* todo : doc *)

Ltac cancel_all_dup l :=
  repeat first
    [ rewrite (permut_cancel_1 l)
    | rewrite (permut_cancel_2 l)
    | rewrite (permut_cancel_3 l)
    | rewrite (permut_cancel_4 l)
    | rewrite (permut_cancel_5 l) ].

Ltac permut_index_of l lcontainer :=
  match constr:(lcontainer) with
  | l \u _ => constr:(1)
  | _ \u l \u _ => constr:(2)
  | _ \u _ \u l \u _ => constr:(3)
  | _ \u _ \u _ \u l \u _ => constr:(4)
  | _ \u _ \u _ \u _ \u l \u _ => constr:(5)
  | _ \u _ \u _ \u _ \u _ \u l \u _ => constr:(6)
  | _ \u _ \u _ \u _ \u _ \u _ \u l \u _ => constr:(7)
  | _ \u _ \u _ \u _ \u _ \u _ \u _ \u l \u _ => constr:(8)
  | _ => constr:(0) (* not found *)
  end.

(** [permut_simplify] simplifies a goal of the form
    [permut l l'] where [l] and [l'] are lists built with
    concatenation and consing, by cancelling syntactically
    equal elements *)

Ltac permut_simpl_once :=
  match goal with
  | |- (_ \u \{}) = _ => fail 1
  | |- (_ \u (?l \u ?lr)) = ?l' =>
     cancel_all_dup l;
     match permut_index_of l l' with
     | 0 => apply permut_tactic_keep
     | ?n => let F := permut_lemma_get n in
            eapply permut_tactic_trans;
            [ eapply F; try typeclass
            | apply permut_tactic_simpl ]
     end
  end.

Ltac permut_simpl :=
  permut_simpl_prepare;
  repeat permut_simpl_once;
  rew_permut_simpl;
  try apply refl_equal.

(* TODO: move demos somewhere else *)

Section DemoSetUnion.
Variables (A:Type).

Lemma demo_set_union_permut_simpl_1 :
  forall l1 l2 l3 : set A,
  (l1 \u l2 \u l3 \u l1) = (l3 \u l2 \u l1).
Proof using.
  intros.
  permut_simpl_prepare.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  rew_permut_simpl.
Qed.


Lemma demo_set_union_permut_simpl_2 :
  forall
  (x:A) l1 l2 l3,
  (l1 \u \{x} \u l3 \u l2) = (l1 \u l2 \u (\{x} \u l3)).
Proof using.
  intros.
  permut_simpl_prepare.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  rew_permut_simpl.
Qed.

Lemma demo_set_union_permut_simpl_3 : forall (x y:A) l1 l1' l2 l3,
  l1 = l1' ->
  (l1 \u (\{x} \u l2) \u \{x} \u (\{y} \u l3)) = (\{y} \u (l1' \u l2) \u (\{x} \u l3)).
Proof using.
  intros.
  permut_simpl_prepare.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  try permut_simpl_once.
  rew_permut_simpl.
Qed.

End DemoSetUnion.

(* ---------------------------------------------------------------------- *)
(** ** Tactics to prove membership *)

(* DEPRECATED: use "set_prove" when possible *)

Section InUnionGet.
Variables (A:Type).
Implicit Types l : set A.

Lemma in_union_get_1 : forall x l1 l2,
  x \in l1 -> x \in (l1 \u l2).
Proof using. intros. apply in_union_l. auto. Qed.

Lemma in_union_get_2 : forall x l1 l2 l3,
  x \in l2 -> x \in (l1 \u l2 \u l3).
Proof using. intros. apply in_union_r. apply~ in_union_get_1. Qed.

Lemma in_union_get_3 : forall x l1 l2 l3 l4,
  x \in l3 -> x \in (l1 \u l2 \u l3 \u l4).
Proof using. intros. apply in_union_r. apply~ in_union_get_2. Qed.

Lemma in_union_get_4 : forall x l1 l2 l3 l4 l5,
  x \in l4 -> x \in (l1 \u l2 \u l3 \u l4 \u l5).
Proof using. intros. apply in_union_r. apply~ in_union_get_3. Qed.

Lemma in_union_get_5 : forall x l1 l2 l3 l4 l5 l6,
  x \in l5 -> x \in (l1 \u l2 \u l3 \u l4 \u l5 \u l6).
Proof using. intros. apply in_union_r. apply~ in_union_get_4. Qed.

End InUnionGet.

Implicit Arguments in_union_get_1 [A x l1 l2].
Implicit Arguments in_union_get_2 [A x l1 l2 l3].
Implicit Arguments in_union_get_3 [A x l1 l2 l3 l4].
Implicit Arguments in_union_get_4 [A x l1 l2 l3 l4 l5].
Implicit Arguments in_union_get_5 [A x l1 l2 l3 l4 l5 l6].

Ltac in_union_get :=
  match goal with H: ?x \in ?A |- ?x \in ?B =>
  match B with context [A] =>
  let go tt := first
        [ apply (in_union_get_1 H)
        | apply (in_union_get_2 H)
        | apply (in_union_get_3 H)
        | apply (in_union_get_4 H)
        | apply (in_union_get_5 H) ] in
  first [ go tt
        | rewrite <- (for_set_union_empty_r B);
          repeat rewrite <- for_set_union_assoc;
          go tt ]
  end end.

Hint Extern 3 (_ \in _ \u _) => in_union_get.

Section InUnionExtract.
Variables (A:Type).
Implicit Types l : set A.

Lemma in_union_extract_1 : forall x l1,
  x \in (\{x} \u l1).
Proof using. intros. apply in_union_get_1. apply in_single_self. Qed.

Lemma in_union_extract_2 : forall x l1 l2,
  x \in (l1 \u \{x} \u l2).
Proof using. intros. apply in_union_get_2. apply in_single_self. Qed.

Lemma in_union_extract_3 : forall x l1 l2 l3,
  x \in (l1 \u l2 \u \{x} \u l3).
Proof using. intros. apply in_union_get_3. apply in_single_self. Qed.

Lemma in_union_extract_4 : forall x l1 l2 l3 l4,
  x \in (l1 \u l2 \u l3 \u \{x} \u l4).
Proof using. intros. apply in_union_get_4. apply in_single_self. Qed.

Lemma in_union_extract_5 : forall x l1 l2 l3 l4 l5,
  x \in (l1 \u l2 \u l3 \u l4 \u \{x} \u l5).
Proof using. intros. apply in_union_get_5. apply in_single_self. Qed.

End InUnionExtract.

Ltac in_union_extract :=
  match goal with |- ?x \in ?A =>
  match A with context [\{x}] =>
  let go tt := first
        [ apply (in_union_extract_1)
        | apply (in_union_extract_2)
        | apply (in_union_extract_3)
        | apply (in_union_extract_4)
        | apply (in_union_extract_5) ] in
  first [ go tt
        | rewrite <- (for_set_union_empty_r A);
          repeat rewrite <- for_set_union_assoc;
          go tt ]
  end end.

Hint Extern 3 (_ \in _) => in_union_extract.


(* ---------------------------------------------------------------------- *)
(** ** Tactics to invert a membership hypothesis *)

(* TODO: document and clean up *)

Section InversionsTactic.
Context (A:Type).
Implicit Types l : set A.
Implicit Types x : A.
Lemma empty_eq_single_inv_1 : forall x l1 l2,
  l1 = l2 -> x \notin l1 -> x \in l2 -> False.
Proof using. intros. subst*. Qed.
Lemma empty_eq_single_inv_2 : forall x l1 l2,
  l1 = l2 -> x \notin l2 -> x \in l1 -> False.
Proof using. intros. subst*. Qed.
Lemma notin_empty : forall x,
  x \notin (\{}:set A).
Proof using. intros. unfold notin. rewrite in_empty_eq. auto. Qed.
End InversionsTactic.
Hint Resolve notin_empty.

Ltac in_union_meta :=
  match goal with
  | |- _ \in \{_} => apply in_single_self
  | |- _ \in \{_} \u _ => apply in_union_l; apply in_single_self
  | |- _ \in _ \u _ => apply in_union_r; in_union_meta
  end.

Ltac fset_inv_core_for H :=
  let go L :=
     false L; [ apply H
              | try apply notin_empty
              | instantiate; try in_union_meta ] in
  match type of H with
  | \{} = _ => go empty_eq_single_inv_1
  | _ = \{} => go empty_eq_single_inv_2
  | _ = _ => go empty_eq_single_inv_1
  end.

Tactic Notation "fset_inv" constr(H) :=
  fset_inv_core_for H.

Ltac fset_inv_core :=
  match goal with
  | |- \{} <> _ => let H := fresh in intro H; fset_inv H
  | |- _ <> \{} => let H := fresh in intro H; fset_inv H
  | H: \{} = _ |- _ => fset_inv H
  | H: _ = \{} |- _ => fset_inv H
  end.

Tactic Notation "fset_inv" :=
  fset_inv_core.

Section InUnionInv.
Variables (A:Type).
Implicit Types l : set A.

Lemma set_in_empty_inv : forall x,
  x \in (\{}:set A) -> False.
Proof using. introv. apply notin_empty. Qed.
Lemma set_in_single_inv : forall x y : A,
  x \in (\{y}:set A) -> x = y.
Proof using. intros. rewrite @in_single_eq in H. auto. typeclass. Qed.
Lemma set_in_union_inv : forall x l1 l2,
  x \in (l1 \u l2) -> x \in l1 \/ x \in l2.
Proof using. introv H. rewrite @in_union_eq in H. auto. typeclass. Qed.

End InUnionInv.

Implicit Arguments set_in_single_inv [A x y].
Implicit Arguments set_in_union_inv [A x l1 l2].


Ltac set_in_inv_base H M :=
  match type of H with
  | _ \in \{} => false; apply (@set_in_empty_inv _ _ H)
  | _ \in \{_} =>
    generalize (set_in_single_inv H); try clear H; intro_subst
  | _ \in _ \u _ =>
    let H' := fresh "TEMP" in
    destruct (set_in_union_inv H) as [H'|H'];
    try clear H; set_in_inv_base H' M
  | _ => rename H into M
  end.

Tactic Notation "set_in" constr(H) "as" ident(M) :=
  set_in_inv_base H M.
Tactic Notation "set_in" constr(H) :=
  let M := fresh "H" in set_in H as M.


(* ---------------------------------------------------------------------- *)
(** ** Tactic to prove two sets equal by double-inclusion *)

(* DEPRECATED: use "set_prove" instead when possible *)

Tactic Notation "eq_set" :=
  let H := fresh "TEMP" in
  apply set_ext; iff H; set_in H; in_union_get.
Tactic Notation "eq_set" "*" :=
  eq_set; auto_star.




(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)

(* FUTURE

  (** Sets of sets *)

  (* todo: typeclass for bigunion and bigintersection *)

  Definition bigunion_impl A (E : set (set A)) : set A :=
    \set{ x | exists_ F \in E, x \in (F:set A) }.

  Definition biguinter_impl A (E : set (set A)) : set A :=
    \set{ x | forall_ F \in E, x \in (F:set A) }.

*)

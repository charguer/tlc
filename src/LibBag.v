(**************************************************************************
* TLC: A library for Coq                                                  *
* Shared definitions for containers                                       *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibReflect
  LibRelation LibOperation LibInt LibStruct.
Generalizable Variables A B K T.

(* ********************************************************************** *)
(** * Operators *)

(* ---------------------------------------------------------------------- *)
(** ** Definitions *)

Class BagEmpty T := { empty : T }.
Class BagSingle A T := { single : A -> T }.
Class BagSingleBind A B T := { single_bind : A -> B -> T }.
Class BagIn A T := { is_in : A -> T -> Prop }.
Class BagBinds A B T := { binds : T -> A -> B -> Prop }.
Class BagRead A B T := { read : T -> A -> B }.
Class BagUpdate A B T := { update : T -> A -> B -> T }.
Class BagUnion T := { union : T -> T -> T }.
Class BagInter T := { inter : T -> T -> T }.
Class BagIncl T := { incl : binary T }.
Class BagDisjoint T := { disjoint : binary T }.
Class BagRestrict T K := { restrict : T -> K -> T }.
Class BagRemove T K := { remove : T -> K -> T }.
Class BagFold I F T := { fold : monoid_def I -> F -> T -> I }.
Class BagCard T := { card : T -> nat }.
Class BagDom T Ks := { dom : T -> Ks }.
Class BagIndex A T := { index : T -> A -> Prop }.

Definition notin `{BagIn A T} x m :=
  ~ (is_in x m).


(* ---------------------------------------------------------------------- *)
(** ** Notation *)

Notation "\{}" := (empty)
  : container_scope.
Notation "\{ x }" := (single x)
  : container_scope.
Notation "x '\in' m" := (is_in x m)
  (at level 39) : container_scope.
Notation "x '\notin' E" := (notin x E)
  (at level 39) : container_scope.
Notation "x \:= v" := (single_bind x v)
  (at level 29) : container_scope.
Notation "m [ x ]" := (read m x)
  (at level 9, format "m [ x ]").
Notation "m [ x := v ]" := (update m x v)
  (at level 9, format "m [ x  :=  v ]").

(* DEPRECATED *)
Notation "m \( x )" := (read m x)
  (at level 33, format "m \( x )", only parsing) : container_scope.
Notation "m \( x := v )" := (update m x v)
  (at level 33, format "m \( x := v )", only parsing) : container_scope.


Notation "m1 '\c' m2" := (incl m1 m2)
  (at level 38) : container_scope.
Notation "m1 '\u' m2" := (union m1 m2)
  (at level 37, right associativity) : container_scope.
Notation "m1 '\n' m2" := (inter m1 m2)
  (at level 36, right associativity) : container_scope.
Notation "m1 '\-' m2" := (remove m1 m2)
  (at level 35) : container_scope.
Notation "m1 '\|' m2" := (restrict m1 m2)
  (at level 34) : container_scope.
Notation "m1 '\#' m2" := (disjoint m1 m2)
  (at level 37, right associativity) : container_scope.

Open Scope container_scope.

(* todo: bug with spaces *)
Notation "''{' x '}'" := (single x) (format "''{' x '}'")
  : container_scope.

Notation "M \-- i" := (M \- \{i}) (at level 35) : container_scope.

(* ---------------------------------------------------------------------- *)
(** ** [forall x \in E, P x] notation *)

Notation "'forall_' x '\in' E ',' P" :=
  (forall x, x \in E -> P)
  (at level 200, x ident) : container_scope.
Notation "'forall_' x y '\in' E ',' P" :=
  (forall x y, x \in E -> y \in E -> P)
  (at level 200, x ident, y ident) : container_scope.
Notation "'forall_' x y z '\in' E ',' P" :=
  (forall x y z, x \in E -> y \in E -> z \in E -> P)
  (at level 200, x ident, y ident, z ident) : container_scope.

(* ---------------------------------------------------------------------- *)
(** ** [exists x \in E st P x] notation *)

Notation "'exists_' x '\in' E ',' P" :=
  (exists x, x \in E /\ P)
  (at level 200, x ident) : container_scope.
Notation "'exists_' x y '\in' E ',' P" :=
  (exists x, x \in E /\ y \in E /\ P)
  (at level 200, x ident, y ident) : container_scope.
Notation "'exists_' x y z '\in' E ',' P" :=
  (exists x, x \in E /\ y \in E /\ z \in E /\ P)
  (at level 200, x ident, y ident, z ident) : container_scope.

(* ---------------------------------------------------------------------- *)
(** ** Foreach *)

Definition foreach `{BagIn A T} (P:A->Prop) (E:T) :=
  forall x, x \in E -> P x.

(* ---------------------------------------------------------------------- *)
(** ** [index] for natural numbers *)


Instance int_index : BagIndex int int.
Proof using. intros. constructor. exact (fun n (i:int) => 0 <= i < n). Defined.

Lemma int_index_def : forall (n i : int),
  index n i = (0 <= i < n).
Proof using. auto. Qed.

Global Opaque int_index.

Lemma int_index_le : forall i n m : int,
  index n i -> n <= m -> index m i.
Proof using. introv. do 2 rewrite @int_index_def. math. Qed.

Lemma int_index_prove : forall (n i : int),
  0 <= i -> i < n -> index n i.
Proof using. intros. rewrite~ int_index_def. Qed.

Lemma int_index_succ : forall n i, n >= 0 ->
  index (n + 1) i = (index n i \/ i = n).
Proof using.
  introv P. do 2 rewrite int_index_def. extens. iff H.
  apply classic_left. math.
  destruct H; math.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Derivable *)

(** Bag update can be defined as bag union with a singleton bag *)

Instance bag_update_as_union_single : forall A B T
  `{BagSingleBind A B T} `{BagUnion T},
  BagUpdate A B T.
  constructor. apply (fun m k v => m \u (k \:= v)). Defined.

Global Opaque bag_update_as_union_single.



(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Section Properties.

Context {A T:Type}
  {BI: BagIn A T} {BE: BagEmpty T} {BS: BagSingle A T}
  {BN: BagInter T} {BU: BagUnion T} {BR: BagRemove T T} {BC: BagCard T}
  {BL: BagIncl T} {BD: BagDisjoint T}.

(** In *)

Class In_empty_eq :=
  { in_empty_eq : forall x, x \in \{} = False }.
Class In_empty :=
  { in_empty : forall x, x \in \{} -> False }.

Class Notin_eq :=
  { notin_eq : forall x E, (x \notin E) = ~ (x \in E) }.
Class Notin_empty :=
  { notin_empty : forall x, x \notin \{} }.

Class In_single_eq :=
  { in_single_eq : forall x y, x \in \{y} = (x = y) }.
Class In_single :=
  { in_single : forall x y, x \in \{y} -> x = y }.
Class In_single_self :=
  { in_single_self : forall x, x \in \{x} }.

Class In_extens_eq :=
  { in_extens_eq : forall E F, (forall x, x \in E = x \in F) -> E = F }.
Class In_extens :=
  { in_extens : forall E F, (forall x, x \in E <-> x \in F) -> E = F }.

Class Is_empty_eq :=
  { is_empty_eq : forall E, (E = \{}) = (forall x, x \in E -> False) }.
Class Is_empty_prove :=
  { is_empty_prove : forall E, (forall x, x \in E -> False) -> E = \{} }.
Class Is_empty_inv :=
  { is_empty_inv : forall x E, E = \{} -> x \in E -> False }.
Class Is_nonempty_prove :=
  { is_nonempty_prove : forall x E, x \in E -> E <> \{} }.

Class Is_single_eq :=
  { is_single_eq : forall x E, (E = \{x}) = (x \in E /\ (forall y, y \in E -> y = x)) }.
Class Is_single_prove :=
  { is_single_prove : forall x E, x \in E -> (forall y, y \in E -> y = x) -> E = \{x} }.
Class Is_single_inv :=
  { is_single_inv : forall x y E, E = \{x} -> y \in E -> y = x }.
Class Notin_single_eq :=
  { notin_single_eq : forall x y, x \notin \{y} = (x <> y) }.

Class In_inter_eq :=
  { in_inter_eq : forall x E F, x \in (E \n F) = (x \in E /\ x \in F) }.
Class In_inter :=
  { in_inter : forall x E F, x \in E -> x \in F -> x \in (E \n F) }.
Class In_inter_inv :=
  { in_inter_inv : forall x E F, x \in (E \n F) -> x \in E /\ x \in F }.

Class Notin_inter_eq :=
  { notin_inter_eq : forall x E F, x \notin (E \n F) = (x \notin E \/ x \notin F) }.
Class Notin_inter_l :=
  { notin_inter_l : forall x E F, x \notin E -> x \notin (E \n F) }.
Class Notin_inter_r :=
  { notin_inter_r : forall x E F, x \notin F -> x \notin (E \n F) }.
Class Notin_inter_inv :=
  { notin_inter_inv : forall x E F, x \notin (E \n F) -> x \notin E \/ x \notin F }.

Class In_union_eq :=
  { in_union_eq : forall x (E F : T), x \in (E \u F) = (x \in E \/ x \in F) }.
Class In_union_l :=
  { in_union_l : forall x E F, x \in E -> x \in (E \u F) }.
Class In_union_r :=
  { in_union_r : forall x E F, x \in F -> x \in (E \u F) }.
Class In_union_inv :=
  { in_union_inv : forall x (E F : T), x \in (E \u F) -> (x \in E \/ x \in F) }.

Class Notin_union_eq :=
  { notin_union_eq : forall x E F, x \notin (E \u F) = (x \notin E /\ x \notin F) }.
Class Notin_union :=
  { notin_union : forall x E F, x \notin E -> x \notin F -> x \notin (E \u F) }.
Class Notin_union_inv :=
  { notin_union_inv : forall x E F, x \notin (E \u F) -> x \notin E /\ x \notin F }.

Class In_remove_eq :=
  { in_remove_eq : forall x (E F : T), x \in (E \- F) = (x \in E /\ x \notin F) }.
Class Remove_incl :=
  { remove_incl : forall (E F : T), (E \- F) \c E }.
Class Remove_disjoint :=
  { remove_disjoint : forall (E F : T), F \# (E \- F) }.

(** Incl *)

Class Incl_in_eq :=
  { incl_in_eq : forall E F, (E \c F) = (forall x, x \in E -> x \in F) }.
Class Incl_prove :=
  { incl_prove : forall E F, (forall x, x \in E -> x \in F) -> E \c F }.
Class Incl_inv :=
  { incl_inv : forall x E F, E \c F -> x \in E -> x \in F}.

Class Incl_refl :=
  { incl_refl : refl incl }.
Class Incl_trans :=
  { incl_trans : trans incl }.
Class Incl_antisym := (* note: double inclusion *)
  { incl_antisym : antisym incl }.
Class Incl_order :=
  { incl_order : LibOrder.order incl }.

Class Empty_incl :=
  { empty_incl : forall E, \{} \c E }.
Class Incl_empty :=
  { incl_empty : forall E, (E \c \{}) = (E = \{}) }.
Class Incl_empty_inv :=
  { incl_empty_inv : forall E, E \c \{} -> E = \{} }.

Class Single_incl_r_eq :=
  { single_incl_r_eq : forall x E, (\{x} \c E) = (x \in E) }.
Class Single_incl_r :=
  { single_incl_r : forall x E, x \in E -> \{x} \c E }.

Class Single_incl_l_eq :=
  { single_incl_l_eq : forall x E, (E \c \{x}) = (E = \{} \/ E = \{x}) }.

Class Incl_union_l :=
  { incl_union_l : forall E F G, E \c F -> E \c (F \u G) }.
Class Incl_union_r :=
  { incl_union_r : forall E F G, E \c G -> E \c (F \u G) }.

Class Union_incl_eq :=
  { union_incl_eq : forall E F G, ((E \u F) \c G) = (E \c G /\ F \c G) }.
Class Union_incl :=
  { union_incl : forall E F G, E \c G -> F \c G -> (E \u F) \c G }.
Class Union_incl_inv :=
  { union_incl_inv : forall E F G, (E \u F) \c G -> E \c G /\ F \c G }.

Class Incl_inter_eq :=
  { incl_inter_eq : forall E F G, E \c (F \n G) = (E \c F /\ E \c G) }.
Class Incl_inter :=
  { incl_inter : forall E F G, E \c F -> E \c G -> E \c (F \n G) }.
Class Incl_inter_inv :=
  { incl_inter_inv : forall E F G, E \c (F \n G) -> E \c F /\ E \c G }.

(** Union *)

Class Union_assoc :=
  { union_assoc : assoc union }.
Class Union_comm :=
  { union_comm : comm union }.
Class Union_comm_assoc :=
  { union_comm_assoc : comm_assoc union }.
Class Union_empty_l :=
  { union_empty_l : neutral_l union empty }.
Class Union_empty_r :=
  { union_empty_r : neutral_r union empty }.
Class Union_empty_inv :=
  { union_empty_inv : forall E F, E \u F = \{} -> E = \{} /\ F = \{} }.
Class Union_self :=
  { union_self : idempotent2 union }.

(** Intersection *)

Class Inter_assoc :=
  { inter_assoc : assoc inter }.
Class Inter_comm :=
  { inter_comm : comm inter }.
Class Inter_comm_assoc :=
  { inter_comm_assoc : comm_assoc inter }.
Class Inter_empty_l :=
  { inter_empty_l : absorb_l inter empty }.
Class Inter_empty_r :=
  { inter_empty_r : absorb_r inter empty }.
Class Inter_self :=
  { inter_self : idempotent2 inter }.


(** Removal *)

  (* TODO: add more *)

(** Cardinal *)

Class Card_empty :=
  { card_empty : card \{} = 0%nat }.
Class Card_single :=
  { card_single : forall X, card \{X} = 1%nat }.
Class Card_union :=
  { card_union : forall E F, E \# F -> card (E \u F) = (card E + card F)%nat }.
Class Card_union_le :=
  { card_union_le : forall E F, card (E \u F) <= (card E + card F)%nat }.

(** Disjointness *)

Class Disjoint_sym :=
  { disjoint_sym : sym disjoint }.
Class Disjoint_eq :=
  { disjoint_eq : forall E F, (E \# F) = (forall x, x \in E -> x \in F -> False) }.
Class Disjoint_not_eq :=
  { disjoint_not_eq : forall E F, (~ (E \# F)) = (exists x, x \in E /\ x \in F) }.
Class Disjoint_prove :=
  { disjoint_prove : forall E F, (forall x, x \in E -> x \in F -> False) -> E \# F }.
Class Disjoint_inv :=
  { disjoint_inv : forall x E F, (E \# F) -> x \in E -> x \in F -> False }.
Class Disjoint_single_l_eq :=
  { disjoint_single_l_eq : forall x E, (\{x} \# E) = x \notin E }.
Class Disjoint_single_r_eq :=
  { disjoint_single_r_eq : forall x E, (E \# \{x}) = x \notin E }.

Class Inter_disjoint :=
  { inter_disjoint : forall E F, E \# F -> E \n F = \{} }.

  (* TODO: add more *)

End Properties.

(** Lemmas with premises and operators in the conclusion
    need additional implicit arguments *)

Implicit Arguments is_empty_inv [[A] [T] [BI] [BE] [Is_empty_inv] x E].
Implicit Arguments is_nonempty_prove [[A] [T] [BE] [Is_nonempty_prove] x E].

Implicit Arguments in_single [A T [BI] [BS] [In_single] [x] [y]].
Implicit Arguments is_single_inv [[A] [T] [BI] [BS] [Is_single_inv] x E].

Implicit Arguments in_inter [[A] [T] [BI] [BN] [In_inter] x E F].
Implicit Arguments in_inter_inv [[A] [T] [BI] [BN] [In_inter_inv] x E F].

Implicit Arguments notin_inter_l [[A] [T] [BI] [BN] [Notin_inter_l] x E F].
Implicit Arguments notin_inter_r [[A] [T] [BI] [BN] [Notin_inter_r] x E F].
Implicit Arguments notin_inter_inv [[A] [T] [BI] [BN] [Notin_inter_inv] x E F].

Implicit Arguments in_union_l [[A] [T] [BI] [BU] [In_union_l] x E F].
Implicit Arguments in_union_r [[A] [T] [BI] [BU] [In_union_r] x E F].
Implicit Arguments in_union_inv [[A] [T] [BI] [BU] [In_union_inv] x E F].

Implicit Arguments notin_union [[A] [T] [BI] [BU] [Notin_union] x E F].
Implicit Arguments notin_union_inv [[A] [T] [BI] [BU] [Notin_union_inv] x E F].

Implicit Arguments incl_prove [[A] [T] [BI] [BL] [Incl_prove] E F].
Implicit Arguments incl_inv [[A] [T] [BI] [BL] [Incl_inv] x E F].
Implicit Arguments incl_trans [[T] [BL] [Incl_trans] x z].
Implicit Arguments incl_empty_inv [[T] [BL] [Incl_empty_inv] E].

Implicit Arguments incl_union_l [[T] [BL] [Incl_union_l] E F G].
Implicit Arguments incl_union_r [[T] [BL] [Incl_union_r] E F G].
Implicit Arguments incl_inter [[T] [BL] [Incl_inter] E F G].
Implicit Arguments incl_inter_inv [[T] [BL] [Incl_inter_inv] E F G].

Implicit Arguments union_empty_inv [[T] [BU] [Union_empty_inv] E F].

Implicit Arguments disjoint_sym [[T] [BD] [Disjoint_sym]].
Implicit Arguments disjoint_prove [[A] [T] [BI] [BD] [Disjoint_prove] E F].
Implicit Arguments disjoint_inv [[A] [T] [BI] [BD] [Disjoint_inv] x E F].
Implicit Arguments disjoint_single_l_eq [[A] [T] [BI] [BS] [BD] [Disjoint_single_l_eq]].
Implicit Arguments disjoint_single_r_eq [[A] [T] [BI] [BS] [BD] [Disjoint_single_r_eq]].


(* ---------------------------------------------------------------------- *)
(** ** Derived Properties *)

Section DerivedProperties.

Context {A T:Type}
  {BI: BagIn A T} {BE: BagEmpty T} {BS: BagSingle A T}
  {BN: BagInter T} {BU: BagUnion T} {BR: BagRemove T T} {BC: BagCard T}
  {BL: BagIncl T} {BD: BagDisjoint T}.

(** In *)

Global Instance in_empty_from_in_empty_eq :
  In_empty_eq -> In_empty.
Proof using. constructor. introv I. rewrite~ in_empty_eq in I. Qed.

Global Instance notin_eq_from_nothing :
  Notin_eq.
Proof using. constructor. intros. unfold notin. auto. Qed.

Global Instance notin_empty_from_in_empty_eq :
  In_empty_eq -> Notin_empty.
Proof using. constructor. introv I. rewrite~ in_empty_eq in I. Qed.

Global Instance in_single_from_in_single_eq :
  In_single_eq -> In_single.
Proof using. constructor. introv I. rewrite~ in_single_eq in I. Qed.

Global Instance in_single_self_from_in_single_eq :
  In_single_eq -> In_single_self.
Proof using. constructor. intros. rewrite~ in_single_eq. Qed.

Global Instance in_extens_eq_from_in_extens :
  In_extens -> In_extens_eq.
Proof using. constructor. introv I. apply in_extens. intros. rewrite* I. Qed.

Global Instance is_empty_eq_from_in_empty_eq :
  In_extens -> In_empty_eq -> Is_empty_eq.
Proof using.
  constructor. intros. extens. iff M.
    subst. introv N. rewrite* in_empty_eq in N.
    apply in_extens. iff N. false* M. rewrite* in_empty_eq in N.
Qed.

Global Instance is_empty_prove_from_is_empty_eq :
  Is_empty_eq -> Is_empty_prove.
Proof using. constructor. introv I. rewrite* is_empty_eq. Qed.

Global Instance is_empty_inv_from_is_empty_eq :
  Is_empty_eq -> Is_empty_inv.
Proof using. constructor. introv I1 I2. rewrite* is_empty_eq in I1. Qed.

Global Instance is_nonempty_prove_from_is_empty_eq :
  Is_empty_eq -> Is_nonempty_prove.
Proof using. constructor. introv I1 I2. rewrite is_empty_eq in I2. eauto. Qed.

Global Instance is_single_eq_from_in_single_eq :
  In_extens -> In_single_eq -> Is_single_eq.
Proof using.
  constructor. intros. extens. iff M (M1&M2).
    subst. split. rewrite* in_single_eq. introv N. rewrite* in_single_eq in N.
    apply in_extens. iff N.
      rewrite* (M2 x0). rewrite* in_single_eq.
      rewrite* in_single_eq in N. subst*.
Qed.

Global Instance is_single_prove_from_is_single_eq :
  Is_single_eq -> Is_single_prove.
Proof using. constructor. introv I. rewrite* is_single_eq. Qed.

Global Instance is_single_inv_from_is_single_eq :
  Is_single_eq -> Is_single_inv.
Proof using. constructor. introv I1 I2. rewrite* is_single_eq in I1. Qed.

Global Instance notin_single_eq_from_in_single_eq :
  In_single_eq -> Notin_single_eq.
Proof using. constructor. intros. unfold notin. rewrite in_single_eq. eauto. Qed.

Global Instance in_inter_from_in_inter_eq :
  In_inter_eq -> In_inter.
Proof using. constructor. introv I1 I2. rewrite in_inter_eq. rew_reflect*. Qed.

Global Instance in_inter_inv_from_in_inter_eq :
  In_inter_eq -> In_inter_inv.
Proof using. constructor. introv I. rewrite~ <- in_inter_eq. Qed.

Global Instance notin_inter_l_from_notin_inter_eq :
  Notin_inter_eq -> Notin_inter_l.
Proof using. constructor. introv I. rewrite~ notin_inter_eq. Qed.

Global Instance notin_inter_r_from_notin_inter_eq :
  Notin_inter_eq -> Notin_inter_r.
Proof using. constructor. introv I. rewrite~ notin_inter_eq. Qed.

Global Instance notin_inter_inv_from_notin_inter_eq :
  Notin_inter_eq -> Notin_inter_inv.
Proof using. constructor. introv I. rewrite~ notin_inter_eq in I. Qed.

Global Instance in_union_l_from_in_union_eq :
  In_union_eq -> In_union_l.
Proof using. constructor. introv I. rewrite in_union_eq. rew_reflect*. Qed.

Global Instance in_union_r_from_in_union_eq :
  In_union_eq -> In_union_r.
Proof using. constructor. introv I. rewrite in_union_eq. rew_reflect*. Qed.

Global Instance in_union_inv_from_in_union_eq :
  In_union_eq -> In_union_inv.
Proof using. constructor. introv I. rewrite~ @in_union_eq in I. Qed.

Global Instance notin_union_from_notin_union_eq :
  Notin_union_eq -> Notin_union.
Proof using. constructor. introv I1 I2. rewrite~ notin_union_eq. Qed.

Global Instance notin_union_inv_from_notin_union_eq :
  Notin_union_eq -> Notin_union_inv.
Proof using. constructor. introv I. rewrite~ notin_union_eq in I. Qed.

  (* TODO: in remove properties?*)

(** Incl *)

Global Instance incl_prove_from_in_eq :
  Incl_in_eq -> Incl_prove.
Proof using. constructor. introv I. rewrite* incl_in_eq. Qed.

Global Instance incl_inv_from_in_eq :
  Incl_in_eq -> Incl_inv.
Proof using. constructor. introv I1 I2. rewrite* incl_in_eq in I1. Qed.

Global Instance incl_order_from_incl_in_eq :
  Incl_in_eq -> In_extens -> Incl_order.
Proof using.
  constructor. constructor.
  intros x. rewrite* incl_in_eq.
  intros E F G I1 I2. rewrite incl_in_eq. rewrite incl_in_eq in I1,I2. autos*.
  intros E F I1 I2. rewrite incl_in_eq in I1,I2. apply* in_extens.
Qed.

Global Instance incl_refl_from_incl_order :
  Incl_order -> Incl_refl.
Proof using. constructor. apply order_refl. apply incl_order. Qed.

Global Instance incl_trans_from_incl_order :
  Incl_order -> Incl_trans.
Proof using. constructor. apply order_trans. apply incl_order. Qed.

Global Instance incl_antisym_from_incl_order :
  Incl_order -> Incl_antisym.
Proof using. constructor. apply order_antisym. apply incl_order. Qed.

Global Instance empty_incl_inv_from_incl_in_eq_and_in_empty_eq :
  Incl_in_eq -> In_empty_eq -> Empty_incl.
Proof using.
  constructor. intros. rewrite incl_in_eq. introv M.
  rewrite in_empty_eq in M. false.
Qed.

Global Instance incl_empty_from_in_empty_eq_and_incl_in_eq :
  In_extens -> In_empty_eq -> Incl_in_eq -> Incl_empty.
Proof using.
  constructor. intros. extens. rewrite incl_in_eq. iff M.
    apply in_extens. iff N. applys* M. rewrite in_empty_eq in N. false.
    subst. introv N. rewrite in_empty_eq in N. false.
Qed.

Global Instance incl_empty_inv_from_incl_empty :
  Incl_empty -> Incl_empty_inv.
Proof using. constructor. introv I. rewrite~ incl_empty in I. Qed.

Global Instance single_incl_r_eq_from_in_single_eq_and_and_incl_in_eq :
  In_extens -> In_single_eq -> Incl_in_eq -> Single_incl_r_eq.
Proof using.
  constructor. intros. extens. rewrite incl_in_eq. iff M.
    applys* M. rewrite~ in_single_eq.
    introv N. rewrite in_single_eq in N. subst~.
Qed.

Global Instance single_incl_r_from_single_incl_r_eq:
  Single_incl_r_eq -> Single_incl_r.
Proof using.
  constructor. intros. rewrite single_incl_r_eq. assumption.
Qed.

Global Instance single_incl_l_eq_from_in_empty_eq_and_in_single_eq_and_and_incl_in_eq :
  In_extens -> In_empty_eq -> In_single_eq -> Incl_in_eq -> Single_incl_l_eq.
Proof using.
  constructor. intros. extens. rewrite incl_in_eq. iff M.
    tests: (x \in E).
      right. apply* is_single_prove. introv N. forwards~ R: M y.
        rewrite* in_single_eq in R.
      left. apply in_extens. iff N. forwards~ R: M x0.
        rewrite* in_single_eq in R. subst. false*.
        rewrite in_empty_eq in N. false.
    introv N. rewrite in_single_eq. destruct M.
      subst. rewrite in_empty_eq in N. false.
      subst. rewrite in_single_eq in N. auto.
Qed.

Global Instance union_incl_eq_from_in_union_eq_and_and_incl_in_eq :
  In_extens -> In_union_eq -> Incl_in_eq -> Union_incl_eq.
Proof using.
  constructor. intros. extens. repeat rewrite incl_in_eq. iff M (M1&M2).
    split. intros x N. specializes M x. rewrite* in_union_eq in M.
           intros x N. specializes M x. rewrite* in_union_eq in M.
    intros x N. specializes M1 x. specializes M2 x. rewrite* in_union_eq in N.
Qed.

Global Instance incl_union_l_from_incl_in_eq_and_in_union_eq :
  Incl_in_eq -> In_union_eq -> Incl_union_l.
Proof using.
  constructor. introv I. rewrite incl_in_eq. rewrite incl_in_eq in I.
  (* coqbug on "rewrite incl_in_eq in *" *)
  introv N. rewrite* in_union_eq.
Qed.

Global Instance incl_union_r_from_incl_union_l :
  Incl_union_l -> Union_comm -> Incl_union_r.
Proof using. constructor. introv I. rewrite union_comm. apply* @incl_union_l. Qed.

Global Instance union_incl_from_union_incl_eq :
  Union_incl_eq -> Union_incl_eq.
Proof using. constructor. intros_all. rewrite union_incl_eq. rew_reflect*. Qed.

Global Instance union_incl_inv_from_union_incl_eq :
  Union_incl_eq -> Union_incl_inv.
Proof using. constructor. introv I. rewrite union_incl_eq in I. destruct* I. Qed.

Global Instance incl_inter_eq_from_in_inter_eq_and_and_incl_in_eq :
  In_extens -> In_inter_eq -> Incl_in_eq -> Incl_inter_eq.
Proof using.
  constructor. intros. extens. repeat rewrite incl_in_eq. iff M (M1&M2).
    split. intros x N. specializes M x. rewrite* in_inter_eq in M.
           intros x N. specializes M x. rewrite* in_inter_eq in M.
    intros x N. specializes M1 N. specializes M2 N. rewrite* in_inter_eq.
Qed.

Global Instance incl_inter_from_incl_inter_eq :
  Incl_inter_eq -> Incl_inter.
Proof using. constructor. intros. rewrite* incl_inter_eq. Qed.

Global Instance incl_inter_inv_from_incl_inter_eq :
  Incl_inter_eq -> Incl_inter_inv.
Proof using. constructor. introv N. rewrite* incl_inter_eq in N. Qed.

(** Tactics *)

Hint Rewrite @in_union_eq @in_inter_eq
  @in_empty_eq @in_single_eq : rew_in_eq.

Tactic Notation "contain_by_in_double" :=
  intros_all; apply in_extens; intros;
  autorewrite with rew_in_eq; rew_reflect;
  intuition (try solve [auto|eauto|auto_false|false]).

(** Union *)

Global Instance union_comm_form_in_union_eq :
  In_extens -> In_union_eq -> Union_comm.
Proof using. constructor. contain_by_in_double. Qed.

Global Instance union_assoc_form_in_union_eq :
  In_extens -> In_union_eq -> Union_assoc.
Proof using. constructor. contain_by_in_double. Qed.

Global Instance union_comm_assoc_from_union_comm_and_union_assoc :
  Union_comm -> Union_assoc -> Union_comm_assoc.
Proof using.
  constructor. intros_all. do 2 rewrite union_assoc.
  rewrite (union_comm _ x). auto.
Qed.

Global Instance union_empty_l_from_in_union_eq_and_in_empty_eq :
  In_extens -> In_union_eq -> In_empty_eq -> Union_empty_l.
Proof using. constructor. contain_by_in_double. Qed.

Global Instance union_empty_r_from_union_empty_l :
  Union_empty_l -> Union_comm -> Union_empty_r.
Proof using. constructor. intros_all. rewrite union_comm. apply union_empty_l. Qed.

Global Instance union_empty_inv_from_in_union_eq :
  In_extens -> In_empty_eq -> In_union_eq -> Union_empty_inv.
Proof using.
  constructor. introv N. split.
    apply in_extens. iff R. rewrite <- N. rewrite* in_union_eq. rewrite* in_empty_eq in R.
    apply in_extens. iff R. rewrite <- N. rewrite* in_union_eq. rewrite* in_empty_eq in R.
Qed.

Global Instance union_self_from_in_union_eq :
  In_extens -> In_union_eq -> Union_self.
Proof using. constructor. contain_by_in_double. Qed.

Global Instance notin_union_eq_from_in_union_eq :
  In_union_eq -> Notin_union_eq.
Proof using. constructor. intros. unfold notin. rewrite @in_union_eq. extens*. eauto. Qed.

(** Inter *)

Global Instance inter_comm_form_in_inter_eq :
  In_extens -> In_inter_eq -> Inter_comm.
Proof using. constructor. contain_by_in_double. Qed.

Global Instance inter_assoc_form_in_inter_eq :
  In_extens -> In_inter_eq -> Inter_assoc.
Proof using. constructor. contain_by_in_double. Qed.

Global Instance inter_comm_assoc_from_inter_comm_and_inter_assoc :
  Inter_comm -> Inter_assoc -> Inter_comm_assoc.
Proof using.
  constructor. intros_all. do 2 rewrite inter_assoc.
  rewrite (inter_comm _ x). auto.
Qed.

Global Instance inter_empty_l_from_in_inter_eq_and_in_empty_eq :
  In_extens -> In_inter_eq -> In_empty_eq -> Inter_empty_l.
Proof using. constructor. contain_by_in_double. Qed.

Global Instance inter_empty_r_from_inter_empty_l :
  Inter_empty_l -> Inter_comm -> Inter_empty_r.
Proof using. constructor. intros_all. rewrite inter_comm. apply inter_empty_l. Qed.

Global Instance inter_self_from_in_inter_eq :
  In_extens -> In_inter_eq -> Inter_self.
Proof using. constructor. contain_by_in_double. Qed.


(** Remove *)

Global Instance remove_incl_from_in_remove_eq_and_incl_in_eq :
  In_remove_eq -> Incl_in_eq -> Remove_incl.
Proof using.
  constructor. intros. rewrite incl_in_eq. introv N. rewrite* in_remove_eq in N.
Qed.

Global Instance remove_disjoint_from_in_remove_eq_and_disjoint_eq :
  In_remove_eq -> Disjoint_eq -> Remove_disjoint.
Proof using.
  constructor. intros. rewrite disjoint_eq. introv N M.
  rewrite* in_remove_eq in M.
Qed.

(** Disjoint *)

Global Instance disjoint_not_eq_from_disjoint_eq :
  Disjoint_eq -> Disjoint_not_eq.
Proof using.
  constructor. intros. rewrite disjoint_eq. extens. iff M.
  { rew_logic in M. destruct M as [x M]. rew_logic* in M. }
  { destruct M as [x M]. rew_logic. exists x. rew_logic*. }  
Qed. (* LATER: rew_logic below binder to simplify proof. *)

Global Instance disjoint_prove_from_disjoint_eq :
  Disjoint_eq -> Disjoint_prove.
Proof using. constructor. intros. rewrite* disjoint_eq. Qed.

Global Instance disjoint_inv_from_disjoint_eq :
  Disjoint_eq -> Disjoint_inv.
Proof using. constructor. introv I I1 I2. rewrite* disjoint_eq in I. Qed.

Global Instance disjoint_single_l_eq_from_disjoint_eq_and_in_single_eq :
  Disjoint_eq -> In_single_eq -> Disjoint_single_l_eq.
Proof using.
  constructor. intros. rewrite disjoint_eq. unfold notin. extens. iff M.
    introv N. specializes M N. rewrite* in_single_eq. false.
    introv N1 N2. rewrite in_single_eq in N1. subst. false.
Qed.

Global Instance disjoint_sym_from_disjoint_eq :
  Disjoint_eq -> Disjoint_sym.
Proof using. constructor. intros x y. do 2 rewrite* disjoint_eq. Qed.

Global Instance disjoint_single_r_eq_from_disjoint_single_l :
  Disjoint_single_l_eq -> Disjoint_sym -> Disjoint_single_r_eq.
Proof using.
  constructor. intros_all.
  rewrite (sym_to_eq disjoint_sym). apply disjoint_single_l_eq.
Qed.

Global Instance inter_disjoint_from_disjoint_eq_and_in_inter_eq :
  In_extens -> In_empty_eq -> Disjoint_eq -> In_inter_eq -> Inter_disjoint.
Proof using.
  constructor. introv M. apply in_extens. rewrite disjoint_eq in M. iff N.
    rewrite in_inter_eq in N. false*.
    rewrite in_empty_eq in N. false.
Qed.


End DerivedProperties.


(**************************************************************************
* TLC: A library for Coq                                                  *
* Binary relations                                                        *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibBool LibLogic LibProd LibSum.
Require Export LibOperation.


(* ********************************************************************** *)
(** * Type of binary relations *)

(* ---------------------------------------------------------------------- *)
(** ** Type of endorelation, i.e. homogeneous binary relations *)

(* TODO: what would be a better name for [binary]? *)

Definition binary (A : Type) := A -> A -> Prop.


(* ---------------------------------------------------------------------- *)
(** ** Inhabited *)

Instance binary_inhab : forall A, Inhab (binary A).
Proof using. intros. apply (prove_Inhab (fun _ _ => True)). Qed.


(* ---------------------------------------------------------------------- *)
(** ** Extensionality *)

Lemma binary_ext : forall A (R1 R2:binary A),
  (forall x y, R1 x y <-> R2 x y) -> 
  R1 = R2.
Proof using. extens*. Qed.

Instance extensionality_binary : forall A, Extensionality (binary A).
Proof using. intros. apply (extensionality_make (@binary_ext A)). Defined.

Lemma rel_eq_inv : forall A (R1 R2:binary A),
  R1 = R2 ->
  (forall x y, R1 x y <-> R2 x y).
Proof using. intros. subst*. Qed.
(* Note: see also [args_eq_2] from LibEqual *)


(* ********************************************************************** *)
(** * Definitions *)

(* ---------------------------------------------------------------------- *)
(** ** Constructions *)

(** LATER: plan to use typeclasses from LibContainer:
    - empty
    - single
    - in
    - binds
    - union
    - inter
    - incl
    - disjoint
    - restrict
    - remove
    - dom
    - img
*)

(** The empty relation 
    TODO: see also typeclass [empty] *)

Definition empty A : binary A :=
  fun x y => False.

(** Union of two relations 
    TODO: see also typeclass [union] *)

Definition union A (R1 R2:binary A) : binary A :=
  fun x y => R1 x y \/ R2 x y.

(** Inverse of a relation *)

Definition inverse A (R:binary A) : binary A :=
  fun x y => R y x.

(** Complement of a relation *)

Definition compl A (R:binary A) : binary A :=
  fun x y => ~ R y x.

(** Strict order associated with an order, wrt Leibnitz' equality *)

Definition strict A (R:binary A) : binary A :=
  fun x y => R x y /\ x <> y.

(** Large order associated with an order, wrt Leibnitz' equality *)

Definition large A (R:binary A) : binary A :=
  fun x y => R x y \/ x = y.

(** Preimage, a.k.a. inverse image *)

Definition rel_preimage (A B:Type) (R:binary B) (f:A->B) : binary A :=
  fun x y => R (f x) (f y).

(** Composition of two relations, usually written [R1; R2]. *)

Definition rel_seq (A B C:Type) (R1:A->B->Prop) (R2:B->C->Prop) : A->C->Prop :=
  fun x z => exists y, R1 x y /\ R2 y z.

(* Turning a function into a relation. *)

Definition rel_fun A B (f:A->B) :=
  fun x y => (y = f x).


(* ---------------------------------------------------------------------- *)
(** ** Closures *)

(** Reflexive-transitive closure ( R* ) *)

Inductive rtclosure (A:Type) (R:binary A) : binary A :=
  | rtclosure_refl : forall x,
      rtclosure R x x
  | rtclosure_step : forall y x z,
      R x y -> 
      rtclosure R y z ->
      rtclosure R x z.

(** Transitive closure ( R+ ), defined as [R \o R*] *)

Inductive tclosure (A:Type) (R:binary A) : binary A :=
  | tclosure_intro : forall x y z,
      R x y -> 
      rtclosure R y z -> 
      tclosure R x z.

(** Another definition of transitive closure ( R+ ) *)

Inductive tclosure' (A:Type) (R:binary A) : binary A :=
  | tclosure'_step : forall x y,
      R x y -> 
      tclosure' R x y
  | tclosure'_trans : forall y x z,
      tclosure' R x y -> 
      tclosure' R y z -> 
      tclosure' R x z.

(** Symmetric closure *)

Definition sclosure (A:Type) (R:binary A) : binary A :=
  fun x y => R x y \/ R y x.

(** Symmetric-transitive closure *)

Inductive stclosure (A:Type) (R:binary A) : binary A :=
  | stclosure_step : forall x y,
      R x y -> 
      stclosure R x y
  | stclosure_sym : forall x y,
      stclosure R x y -> 
      stclosure R y x
  | stclosure_trans : forall y x z,
      stclosure R x y -> 
      stclosure R y z -> 
      stclosure R x z.

(** Reflexive-symmetric-transitive closure *)

Inductive rstclosure (A:Type) (R:binary A) : binary A :=
  | rstclosure_step : forall x y,
      R x y -> 
      rstclosure R x y
  | rstclosure_refl : forall x,
      rstclosure R x x
  | rstclosure_sym : forall x y,
      rstclosure R x y ->
      rstclosure R y x
  | rstclosure_trans : forall y x z,
      rstclosure R x y -> 
      rstclosure R y z -> 
      rstclosure R x z.


(* ---------------------------------------------------------------------- *)
(** ** Properties of relations *)

(** Reflexivity *)

Definition refl A (R:binary A) :=
  forall x, R x x.

(** Irreflexivity *)

Definition irrefl A (R:binary A) :=
  forall x, ~ (R x x).

(** Transitivity *) 

Definition trans A (R:binary A) :=
  forall y x z, R x y -> R y z -> R x z.

(** Symmetry *)

Definition sym A (R:binary A) :=
  forall x y, R x y -> R y x.

(** Asymmetry *)

Definition asym A (R:binary A) :=
  forall x y, R x y -> ~ R y x.

(** Antisymmetry *)

Definition antisym A (R:binary A) :=
  forall x y, R x y -> R y x -> x = y.
  (* same as: [antisym_wrt (@eq A)] *)

(** Antisymmetry with respect to an equivalence relation *)

Definition antisym_wrt A (E:binary A) R :=
  forall x y, R x y -> R y x -> E x y.

(** Totality *)

Definition total A (R:binary A) :=
  forall x y, R x y \/ R y x.

(** Definedness *)

Definition defined A B (R:A->B->Prop) :=
  forall x, exists y, R x y.

(** Functionality *)

Definition functional A B (R:A->B->Prop) :=
  forall x y z, R x y -> R x z -> y = z.

(** Inclusion
    TODO: see also typeclass [incl] *)

Definition rel_incl A B (R1 R2:A->B->Prop) :=
  forall x y, R1 x y -> R2 x y.

(** Equivalence relation *)

Record equiv A (R:binary A) :=
 { equiv_refl : refl R;
   equiv_sym : sym R;
   equiv_trans : trans R }.


(* ---------------------------------------------------------------------- *)
(** ** Pointwise product *)

Definition prod2 (A1 A2:Type) 
  (R1:binary A1) (R2:binary A2) 
   : binary (A1*A2) :=
  fun p1 p2 : A1*A2 => match p1,p2 with (x1,x2),(y1,y2) =>
    R1 x1 y1 /\ R2 x2 y2 end.

Definition prod3 (A1 A2 A3:Type)
  (R1:binary A1) (R2:binary A2) (R3:binary A3)
   : binary (A1*A2*A3) :=
  prod2 (prod2 R1 R2) R3.

Definition prod4 (A1 A2 A3 A4:Type)
  (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4)
   : binary (A1*A2*A3*A4) :=
  prod2 (prod3 R1 R2 R3) R4.

Tactic Notation "unfold_prod" :=
  unfold prod4, prod3, prod2.
Tactic Notation "unfolds_prod" :=
  unfold prod4, prod3, prod2 in *.


(* ---------------------------------------------------------------------- *)
(** ** Lexicographical order *)

Definition lexico2 {A1 A2} (R1:binary A1) (R2:binary A2)
   : binary (A1*A2) :=
  fun p1 p2 : A1*A2 => let (x1,x2) := p1 in let (y1,y2) := p2 in
  (R1 x1 y1) \/ (x1 = y1) /\ (R2 x2 y2).

Definition lexico3 {A1 A2 A3}
   (R1:binary A1) (R2:binary A2) (R3:binary A3) : binary (A1*A2*A3) :=
  lexico2 (lexico2 R1 R2) R3.

Definition lexico4 {A1 A2 A3 A4}
   (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4)
   : binary (A1*A2*A3*A4) :=
  lexico2 (lexico3 R1 R2 R3) R4.

Tactic Notation "unfold_lexico" :=
  unfold lexico4, lexico3, lexico2.
Tactic Notation "unfolds_lexico" :=
  unfold lexico4, lexico3, lexico2 in *.


(* ********************************************************************** *)
(** * Properties *)

Section ConstructionsProp.
Variable (A : Type).
Implicit Types R : binary A.
Implicit Types x y z : A.


(* ---------------------------------------------------------------------- *)
(** ** [refl] *)

Lemma refl_inv : forall x y R,
  refl R -> 
  x = y ->
  R x y.
Proof using. intros_all. subst~. Qed.


(* ---------------------------------------------------------------------- *)
(** ** [sym] *)

Lemma sym_inv : forall x y R,
  sym R -> 
  R x y -> 
  R y x.
Proof using. introv Sy R1. apply* Sy. Qed.

Lemma sym_inv_eq : forall R,
  sym R ->
  (forall x y, R x y = R y x).
Proof using. introv H. intros. apply prop_ext. split; apply H. Qed.

Lemma sym_to_eq : forall x y R,
  sym R ->
  R x y = R y x.
Proof using. introv H. intros. apply prop_ext. split; apply H. Qed.


(* ---------------------------------------------------------------------- *)
(** ** [antisym] *)

Lemma antisym_inv : forall x y R,
  antisym R -> 
  R x y -> 
  R y x -> 
  x <> y -> 
  False.
Proof using. intros_all*. Qed.


(* ---------------------------------------------------------------------- *)
(** ** [irrefl] *)

Lemma irrefl_inv : forall x R,
  irrefl R ->
  R x x -> 
  False.
Proof using. introv H P. apply* H. Qed.

Lemma irrefl_inv_neq : forall R,
  irrefl R ->
  (forall x y, R x y -> x <> y).
Proof using. introv H P E. subst. apply* H. Qed.

Lemma irrefl_neq : forall x y R,
  irrefl R ->
  R x y -> 
  x <> y.
Proof using. intros. applys* irrefl_inv_neq. Qed.


(* ---------------------------------------------------------------------- *)
(** ** [trans] *)

Lemma trans_inv : forall y x z R,
  trans R -> 
  R x y -> 
  R y z -> 
  R x z.
Proof using. introv Tr R1 R2. apply* Tr. Qed.

Lemma trans_inv_swap : forall y x z R,
  trans R -> 
  R y z -> 
  R x y -> 
  R x z.
Proof using. introv Tr R1 R2. apply* Tr. Qed.


(* ---------------------------------------------------------------------- *)
(** ** [trans] + [sym]  *)

Definition trans_sym_ll := trans_inv.

Lemma trans_sym_lr : forall y x z R,
  trans R -> 
  sym R -> 
  R x y -> 
  R z y -> 
  R x z.
Proof using. introv Tr Sy R1 R2. apply* Tr. Qed.

Lemma trans_sym_rr : forall y x z R,
  trans R -> 
  sym R -> 
  R y x -> 
  R z y -> 
  R x z.
Proof using. introv Tr Sy R1 R2. apply* Tr. Qed.

Lemma trans_sym_rl : forall y x z R,
  trans R -> 
  sym R -> 
  R y x -> 
  R y z -> 
  R x z.
Proof using. introv Tr Sy R1 R2. apply* Tr. Qed.


(* ---------------------------------------------------------------------- *)
(** ** [equiv] *)

(** Equality is an equivalence relation *)

Lemma equiv_eq : forall A, 
  equiv (@eq A).
Proof using. intros. constructor; intros_all; subst~. Qed.

Hint Resolve equiv_eq.


(* ---------------------------------------------------------------------- *)
(** ** [incl] *)

Lemma refl_rel_incl : forall A B,
  refl (@rel_incl A B).
  (* forall (R:A->B->Prop), rel_incl R R *)
Proof. unfolds refl, rel_incl. autos*. Qed.

Hint Resolve refl_rel_incl.

Lemma antisym_rel_incl : forall A B, 
  antisym (@rel_incl A B).
  (* forall R1 R2, rel_incl R1 R2 -> rel_incl R2 R1 -> R1 = R2. *)
Proof using. unfolds rel_incl. extens*. Qed.
  (* See also extensionality_pred_2 from LibEqual *)

Lemma trans_rel_incl : forall A B,
  trans (@rel_incl A B).
Proof using. unfold trans, rel_incl. autos*. Qed.  
  (* forall R1 R2 R3, rel_incl R1 R2 -> rel_incl R2 R3 ->  rel_incl R1 R3. *)

(* TODO: requires liborder
Lemma order_rel_incl : forall A B,
  order (@rel_incl A B).
Proof using. 
  hint refl_rel_incl, antisym_rel_incl, trans_rel_incl.
  constructors*.
Qed.
*)


(* ---------------------------------------------------------------------- *)
(** ** [inverse] *)

Lemma injective_inverse : 
  injective (@inverse A).
Proof using.
  intros R1 R2 E. extens. intros x y.
  unfolds inverse. rewrite* (fun_eq_2 y x E).
Qed.

Lemma inverse_sym : forall R,
  sym R -> 
  inverse R = R.
Proof using. intros. unfold inverse. extens*. Qed.

Lemma inverse_inverse : forall R,
  inverse (inverse R) = R.
Proof using. extens*. Qed.

Lemma inverse_eq_l : forall R2 R1,
  R1 = inverse R2 -> 
  inverse R1 = R2.
Proof using. intros. apply injective_inverse. rewrite~ inverse_inverse. Qed.

Lemma inverse_eq_r : forall R2 R1,
  inverse R1 = R2 -> 
  R1 = inverse R2.
Proof using. intros. apply injective_inverse. rewrite~ inverse_inverse. Qed.

Lemma refl_inverse : forall R,
  refl R -> 
  refl (inverse R).
Proof using. intros_all. unfolds inverse. auto. Qed.

Lemma trans_inverse : forall R,
  trans R -> 
  trans (inverse R).
Proof using. intros_all. unfolds inverse. eauto. Qed.

Lemma antisym_inverse : forall R,
  antisym R -> 
  antisym (inverse R).
Proof using. intros_all. unfolds inverse. auto. Qed.

Lemma asym_inverse : forall R,
  asym R -> 
  asym (inverse R).
Proof using. intros_all. unfolds inverse. apply* H. Qed.

Lemma total_inverse : forall R,
  total R -> 
  total (inverse R).
Proof using. intros_all. unfolds inverse. auto. Qed.

Lemma inverse_equiv : forall A (E:binary A),
  equiv E -> 
  equiv (inverse E).
Proof using.
  introv Equi. unfold inverse. constructor; intros_all;
    dintuition eauto.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** [large] *)

Lemma large_trans_l : forall y x z R,
  trans R -> 
  large R x y -> 
  R y z -> 
  R x z.
Proof using. introv T [E|H] H'; subst*. Qed.

Lemma large_trans_r : forall y x z R,
  trans R -> 
  R x y -> 
  large R y z -> 
  R x z.
Proof using. introv T H [E|H']; subst*. Qed.

Lemma refl_large : forall R,
  refl (large R).
Proof using. unfold large. intros_all~. Qed.

Lemma trans_large : forall R,
  trans R -> 
  trans (large R).
Proof using. unfold large. introv Tr [H1|E1] [H2|E2]; subst*. Qed.

Lemma antisym_large : forall R,
  antisym R -> 
  antisym (large R).
Proof using. introv T. introv H1 H2. (* todo: bug introv *)
  unfolds large. destruct H1; destruct H2; auto. Qed.

Lemma total_large : forall R,
  total R -> 
  total (large R).
Proof using. unfold large. intros_all~. destruct* (H x y). Qed.

Lemma large_strict : forall R,
  refl R -> 
  large (strict R) = R.
Proof using.
  unfold large, strict. extens. intros x y. iff K.
  { destruct K; subst*. }
  { tests: (x = y); subst*. }
Qed.

Lemma inverse_large : forall R,
  inverse (large R) = large (inverse R).
Proof using. intros. unfold inverse, large. extens*. Qed.


(* ---------------------------------------------------------------------- *)
(** ** [strict] *)

Lemma inverse_strict : forall R,
  inverse (strict R) = strict (inverse R).
Proof using. intros. unfold inverse, strict. extens*. Qed.

Lemma trans_strict_from_antisym : forall R,
  trans R -> 
  antisym R -> 
  trans (strict R).
Proof using.
  introv T S. unfold strict. introv [H1 H2] [H3 H4]. split.
  { apply* T. }
  { intros K. subst. apply H2. apply~ S. }
Qed.

Lemma strict_large : forall R,
  irrefl R -> 
  strict (large R) = R.
Proof using.
  unfold large, strict. extens. intros x y. iff K.
  { autos*. }
  { split. { left*. } { apply* irrefl_neq. } }
Qed.


(* ---------------------------------------------------------------------- *)
(** ** [functional] *)

(** The empty relation is functional. *)

Lemma functional_empty : 
  functional (@empty A).
Proof using. unfold empty. hnfs*. Qed.

(** The union of two functional relations is functional,
    provided the relations have disjoint domains. *)

Lemma functional_union : forall R1 R2,
  functional R1 ->
  functional R2 ->
  (forall x y z, R1 x y -> R2 x z -> False) ->
  functional (union R1 R2).
Proof using.
  intros. unfold union. intros x y z Hxy Hxz.
  destruct Hxy; destruct Hxz; auto_false*.
Qed.

(** A relation [R] is functional if and only if [inverse R] composed
    with [R] is a subset of the diagonal relation [eq]. *)

Lemma functional_iff_seq_inverse_incl_eq : forall R,
  functional R <->
  rel_incl (rel_seq (inverse R) R) eq.
Proof using.
  unfold functional, rel_incl, rel_seq, inverse. iff; jauto.
Qed.

(** If [R1] is defined, [R2] is functional, and [R1] is a subset of [R2],
    then [R1] equals [R2]. In that case, [R1] and [R2] represent the graph
    of a total function. *)

Lemma eq_from_incl_defined_functional : forall R1 R2,
  defined R1 ->
  functional R2 ->
  rel_incl R1 R2 ->
  R1 = R2.
Proof using.
  introv Hdef Hfun Hincl. extens. intros x y. iff M.
  { eauto. }
  { forwards (w'&M1): Hdef x.
    forwards M2: Hincl M1.
    forwards: Hfun M M2. subst*. }
Qed.

(* TODO: define a tactic "functional_exploit R" that looks for two distinct
   assumptions in the goal of the form [R ?x ?y] and produces [functional R]
   as subgoal, and provides the equality [?y1 = ?y2]. *)


(* ---------------------------------------------------------------------- *)
(** ** [union] *)

Lemma union_l : forall R1 R2 x y,
  R1 x y ->
  union R1 R2 x y.
Proof using. unfold union. eauto. Qed.

Lemma union_r : forall R1 R2 x y,
  R2 x y ->
  union R1 R2 x y.
Proof using. unfold union. eauto. Qed.

Lemma refl_union_l : forall R1 R2,
  refl R1 ->
  refl (union R1 R2).
Proof using. unfold refl, union. eauto. Qed.

Lemma refl_union_r : forall R1 R2,
  refl R2 ->
  refl (union R1 R2).
Proof using. unfold refl, union. eauto. Qed.

Lemma comm_union : 
  comm (@union A).
  (* forall R1 R2, union R1 R2 = union R2 R1. *)
Proof. unfold union. extens*. Qed.

Lemma comm_union_args : forall R1 R2 x y,
  union R2 R1 x y ->
  union R1 R2 x y.
Proof. intros. rewrite~ comm_union. Qed.

(* TODO: generic definition of covariant? *)
Lemma union_covariant : forall R1 R2 S1 S2,
  rel_incl R1 S1 ->
  rel_incl R2 S2 ->
  rel_incl (union R1 R2) (union S1 S2).
Proof using. unfold rel_incl, union. autos*. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Arguments *)

End ConstructionsProp.

Arguments trans_inv [A] y [x] [z] [R].
Arguments trans_inv_swap [A] y [x] [z] [R].
Arguments trans_sym_rr [A] y [x] [z] [R].
Arguments trans_sym_lr [A] y [x] [z] [R].
Arguments trans_sym_rl [A] y [x] [z] [R].


(* ---------------------------------------------------------------------- *)
(** ** [prod] *)

Lemma prod2_equiv : forall A1 A2 (E1:binary A1) (E2:binary A2),
  equiv E1 ->
  equiv E2 -> 
  equiv (prod2 E1 E2).
Proof using.
  introv [R1 S1 T1] [R2 S2 T2]. constructor.
  { intros [x1 x2]. simple*. }
  { intros [x1 x2] [y1 y2]. simple*. }
  { intros [x1 x2] [y1 y2] [z1 z2]. simple*. }
Qed.

(* TODO: other arities of Prod *)


(* ---------------------------------------------------------------------- *)
(** ** [lexico] *)

Section LexicoApp.
Variables (A1 A2 A3 A4:Type).
Variables (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4).

Lemma lexico2_1 : forall x1 x2 y1 y2,
  R1 x1 y1 ->
  lexico2 R1 R2 (x1,x2) (y1,y2).
Proof using. intros. left~. Qed.

Lemma lexico2_2 : forall x1 x2 y1 y2,
  x1 = y1 -> 
  R2 x2 y2 ->
  lexico2 R1 R2 (x1,x2) (y1,y2).
Proof using. intros. right~. Qed.

Lemma lexico3_1 : forall x1 x2 x3 y1 y2 y3,
  R1 x1 y1 ->
  lexico3 R1 R2 R3 (x1,x2,x3) (y1,y2,y3).
Proof using. intros. left. left~. Qed.

Lemma lexico3_2 : forall x1 x2 x3 y1 y2 y3,
  x1 = y1 -> 
  R2 x2 y2 ->
  lexico3 R1 R2 R3 (x1,x2,x3) (y1,y2,y3).
Proof using. intro. left. right~. Qed.

Lemma lexico3_3 : forall x1 x2 x3 y1 y2 y3,
  x1 = y1 -> 
  x2 = y2 -> 
  R3 x3 y3 ->
  lexico3 R1 R2 R3 (x1,x2,x3) (y1,y2,y3).
Proof using. intros. right~. Qed.

Lemma lexico4_1 : forall x1 x2 x3 x4 y1 y2 y3 y4,
  R1 x1 y1 ->
  lexico4 R1 R2 R3 R4 (x1,x2,x3,x4) (y1,y2,y3,y4).
Proof using. intros. left. left. left~. Qed.

Lemma lexico4_2 : forall x1 x2 x3 x4 y1 y2 y3 y4,
  x1 = y1 -> 
  R2 x2 y2 ->
  lexico4 R1 R2 R3 R4 (x1,x2,x3,x4) (y1,y2,y3,y4).
Proof using. intros. left. left. right~. Qed.

Lemma lexico4_3 : forall x1 x2 x3 x4 y1 y2 y3 y4,
  x1 = y1 -> 
  x2 = y2 -> 
  R3 x3 y3 ->
  lexico4 R1 R2 R3 R4 (x1,x2,x3,x4) (y1,y2,y3,y4).
Proof using. intros. left. right~. Qed.

Lemma lexico4_4 : forall x1 x2 x3 x4 y1 y2 y3 y4,
  x1 = y1 -> 
  x2 = y2 -> 
  x3 = y3 -> 
  R4 x4 y4 ->
  lexico4 R1 R2 R3 R4 (x1,x2,x3,x4) (y1,y2,y3,y4).
Proof using. intros. right~. Qed.

End LexicoApp.

(** Transitivity *)

Lemma trans_lexico2 : forall A1 A2
   (R1:binary A1) (R2:binary A2),
  trans R1 -> 
  trans R2 -> 
  trans (lexico2 R1 R2).
Proof using.
  introv Tr1 Tr2. intros [x1 x2] [y1 y2] [z1 z2] Rxy Ryz.
  simpls. destruct Rxy as [L1|[Eq1 L1]];
   destruct Ryz as [M2|[Eq2 M2]]; subst*.
Qed.

Lemma trans_lexico3 : forall A1 A2 A3
   (R1:binary A1) (R2:binary A2) (R3:binary A3),
  trans R1 -> 
  trans R2 -> 
  trans R3 -> 
  trans (lexico3 R1 R2 R3).
Proof using.
  introv Tr1 Tr2 Tr3. applys~ trans_lexico2. applys~ trans_lexico2.
Qed.

Lemma trans_lexico4 : forall A1 A2 A3 A4
   (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4),
  trans R1 ->
  trans R2 ->
  trans R3 -> 
  trans R4 -> 
  trans (lexico4 R1 R2 R3 R4).
Proof using.
  introv Tr1 Tr2 Tr3. applys~ trans_lexico3. applys~ trans_lexico2.
Qed.

(** Inclusion *)

Lemma rel_incl_lexico2 : forall A1 A2
   (R1 R1':binary A1) (R2 R2':binary A2),
  rel_incl R1 R1' -> 
  rel_incl R2 R2' -> 
  rel_incl (lexico2 R1 R2) (lexico2 R1' R2').
Proof using.
  introv I1 I2. intros [x1 x2] [y1 y2] [H1|[H1 H2]].
  { left~. } { subst. right~. }
Qed.

(* TODO: other arities for inclusion *)



(**************************************************************************)
(* * Closures *)

(* ---------------------------------------------------------------------- *)
(** ** Basic properties of closures *)

(* TODO: complete by adding more lemmas *)

Section Closures.
Variables (A : Type).
Implicit Types R : binary A.
Hint Constructors tclosure rtclosure equiv.

(** [rtclosure] *)

Lemma rtclosure_once : forall R x y,
  R x y -> 
  rtclosure R x y.
Proof using. autos*. Qed.

Hint Resolve rtclosure_once.

Lemma trans_rtclosure : forall R,
  trans (rtclosure R).
Proof using. intros R y x z M1. induction* M1. Qed.

Lemma rtclosure_last : forall R y x z,
  rtclosure x y -> 
  R y z -> 
  rtclosure x z.
Proof using. introv R1 R2. induction* R1. Qed.

Hint Resolve trans_rtclosure.

(** [tclosure] *)

Lemma tclosure_once : forall R x y,
  R x y -> 
  tclosure x y.
Proof using. eauto. Qed.

Hint Resolve tclosure_once.

(** [rtclosure] *)

Lemma rtclosure_from_tclosure : forall R x y,
  tclosure x y -> 
  rtclosure x y.
Proof using. intros. destruct* H. Qed.

Hint Resolve rtclosure_from_tclosure.

---

Lemma tclosure_rtclosure_step : forall R x y z,
  rtclosure x y -> 
  R y z -> 
  tclosure x z.
Proof using. intros. induction* H. Qed.

Lemma tclosure_tclosure_step : forall R x y z,
  tclosure x y -> 
  R y z -> 
  tclosure x z.
Proof. introv C H. applys tclosure_rtclosure_step H. apply* tclosure_rtclosure. Qed.

Lemma tclosure_step_rtclosure : forall R x y z,
  R x y -> 
  rtclosure y z -> 
  tclosure x z.
Proof using. intros. gen x. induction* H0. Qed.

Lemma tclosure_step_tclosure : forall R x y z,
  R x y -> 
  tclosure y z -> 
  tclosure x z.
Proof using. intros. inverts* H0. Qed.

Hint Resolve tclosure_rtclosure_step tclosure_step_rtclosure.

Lemma tclosure_rtclosure_tclosure : forall R y x z,
  rtclosure x y -> 
  tclosure y z -> 
  tclosure x z.
Proof using. intros. gen z. induction* H. Qed.

Lemma tclosure_tclosure_rtclosure : forall R y x z,
  tclosure x y -> 
  rtclosure y z -> 
  tclosure x z.
Proof using. intros. induction* H. Qed.

Lemma trans_tclosure : 
  trans tclosure.
Proof using. intros_all. autos* tclosure_tclosure_rtclosure. Qed.

Lemma tclosure_tclosure' : forall R x y,
  tclosure x y <-> tclosure' x y.
Proof.
  introv. iff C.
   destruct C as [x y z HR HC]. gen x. induction HC; introv HR.
    apply~ tclosure'_step.
    applys~ tclosure'_trans x. constructors~.
   induction C.
    constructors*.
    apply* tclosure_trans.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Induction *)

(** TODO: move induction principles higher up *)

(** Star induction principle with transitivity hypothesis *)

Lemma rtclosure_ind_trans : forall (P : A -> A -> Prop),
  (forall x : A, P x x) ->
  (forall x y : A, R x y -> P x y) ->
  (forall y x z : A, rtclosure x y -> P x y -> rtclosure y z -> P y z -> P x z) ->
  forall x y : A, rtclosure x y -> P x y.
Proof using.
  introv Hrefl Hstep Htrans S. induction S.
  auto. apply~ (@Htrans y).
Qed.

(** Star induction principle with steps at the end *)

Lemma rtclosure_ind_r : forall (P : A -> A -> Prop),
  (forall x : A, P x x) ->
  (forall y x z : A, rtclosure x y -> P x y -> R y z -> P x z) ->
  forall x y : A, rtclosure x y -> P x y.
Proof using.
  introv Hrefl Hlast. apply rtclosure_ind_trans.
  auto.
  intros. apply~ (Hlast x).
  introv S1 P1 S2 _. gen x. induction S2; introv S1 P1.
     auto.
     apply IHS2. eauto. apply~ (Hlast x).
Qed.

End Closures.

(** Star induction principle with transitivity hypothesis *)

Lemma tclosure_ind_trans : forall A (R:binary A) (P : A -> A -> Prop),
  (forall x y : A, R x y -> P x y) ->
  (forall y x z : A, tclosure R x y -> P x y -> tclosure R y z -> P y z -> P x z) ->
  forall x y : A, tclosure R x y -> P x y.
Proof using.
  Hint Resolve tclosure_once.
  introv Hstep Htrans S. inverts S as HR S. gen x. induction S; introv HR.
    autos*.
    applys* Htrans. constructors*.
Qed.

(** Star induction principle with steps at the end *)

Lemma tclosure_ind_r : forall A (R : binary A) (P : A -> A -> Prop),
  (forall x y, R x y -> P x y) ->
  (forall y x z, tclosure R x y -> P x y -> R y z -> P x z) ->
  forall x y, tclosure R x y -> P x y.
Proof.
  introv S Ind H. inverts H as HR HC.
  induction HC using rtclosure_ind_right.
   apply* S.
   applys Ind; try apply* tclosure_step_rtclosure; autos*.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Hints *)

Hint Resolve stclosure_step stclosure_sym stclosure_trans.
(* TODO: remove *)

Hint Resolve rtclosure_refl rtclosure_step rtclosure_once : rtclosure.

Hint Constructors tclosure : tclosure.
Hint Constructors rstclosure : rstclosure.
Hint Constructors stclosure : stclosure.
Hint Unfold sclosure : sclosure.
(* TODO: complete *)


(* ---------------------------------------------------------------------- *)
(** ** Additional properties : TODO: cleanup *)

Lemma tclosure_inv_r : forall A (R : binary A) x y,
  tclosure R x y ->
  exists z, rtclosure R x z /\ R z y.
Proof.
  introv H. induction H using tclosure_ind_right.
   exists x. splits~. constructors~.
   exists y. splits~. apply~ tclosure_rtclosure.
Qed.

Lemma rel_incl_tclosure : forall A (R:binary A),
  rel_incl R (tclosure R).
Proof using. unfolds rel_incl. intros. apply~ tclosure_once. Qed.

Hint Resolve rel_incl_tclosure_self.

Lemma stclosure_le : forall A (R1 R2 : binary A),
  rel_incl R1 R2 -> 
  rel_incl (stclosure R1) (stclosure R2).
Proof using. 
  hint rel_incl_tclosure stclosure_step stclosure_sym stclosure_trans.
  (* TODO: check hints useful *)
  unfolds rel_incl. introv Le H. induction* H. 
Qed.

Lemma rtclosure_refl_contrapositive : forall A (R : binary A) x y,
  ~ rtclosure R x y ->
  x <> y.
Proof using.
  intros. intro. subst. eauto using rtclosure_refl.
Qed.

Lemma rtclosure_rstclosure : forall A (R : binary A) x y,
  rtclosure R x y -> rstclosure R x y.
Proof using.
  induction 1; eauto with rstclosure.
Qed.

Lemma stclosure_rstclosure : forall A (R : binary A) x y,
  stclosure R x y -> rstclosure R x y.
Proof using.
  induction 1; eauto with rstclosure.
Qed.

Lemma stclosure_is_rstclosure : forall A (R : binary A),
  refl R ->
  stclosure R = rstclosure R.
Proof using.
  intros. eapply binary_extensional. intros x y.
  split; eauto using stclosure_rstclosure.
  gen x y. induction 1; eauto with stclosure.
Qed.

Lemma refl_rstclosure : forall A (R : binary A),
  refl (rstclosure R).
Proof using.
  unfold refl. eauto with rstclosure.
Qed.

Lemma rstclosure_covariant : forall A (R S : binary A),
  rel_incl R S ->
  rel_incl (rstclosure R) (rstclosure S).
Proof using.
  unfold rel_incl. induction 2; eauto with rstclosure.
Qed.

Lemma rstclosure_inflationary: forall A (R : binary A),
  rel_incl R (rstclosure R).
Proof using.
  unfold rel_incl. eauto with rstclosure.
Qed.

Lemma prove_rstclosure_rel_incl : forall A (R S : binary A),
  rel_incl R (rstclosure S) ->
  rel_incl (rstclosure R) (rstclosure S).
Proof using.
  unfold rel_incl. induction 2; eauto with rstclosure.
Qed.

Lemma rtclosure_union : forall A (R S : binary A),
  rel_incl (union (rtclosure R) (rtclosure S))
           (rtclosure (union R S)).
Proof using.
  unfold rel_incl, union. intros ? ? ? x y H.
  destruct H; gen x y;
  induction 1; eauto with rtclosure.
Qed.

Lemma rstclosure_union : forall A (R S : binary A),
  rel_incl (union (rstclosure R) (rstclosure S))
       (rstclosure (union R S)).
Proof using.
  unfold rel_incl, union. intros ? ? ? x y H.
  destruct H; gen x y;
  induction 1; eauto with rstclosure.
Qed.


Lemma sym_sclosure : forall A (R : binary A),
  sym (sclosure R).
Proof using.
  unfold sym, sclosure. tauto.
Qed.

Lemma sclosure_is_a_closure_operator : forall A (R1 R2 : binary A),
  rel_incl R1 (sclosure R2) ->
  rel_incl (sclosure R1) (sclosure R2).
Proof using.
  unfold sclosure, rel_incl. introv h. introv H.
  destruct H.
  { eauto. }
  { forwards M: h. eauto. destruct M; tauto. }
Qed.

Lemma sclosure_covariant : forall A (R1 R2 : binary A),
  rel_incl R1 R2 ->
  rel_incl (sclosure R1) (sclosure R2).
Proof using.
  unfold sclosure, rel_incl. introv M H. destruct H; eauto.
Qed.

Lemma rtclosure_covariant : forall A (R1 R2 : binary A),
  rel_incl R1 R2 ->
  rel_incl (rtclosure R1) (rtclosure R2).
Proof using.
  unfold rel_incl. induction 2; eauto with rtclosure.
Qed.

Lemma tclosure_covariant : forall A (R1 R2 : binary A),
  rel_incl R1 R2 ->
  rel_incl (tclosure R1) (tclosure R2).
Proof using.
  unfold rel_incl. inversion 2; subst. econstructor.
  eauto.
  eapply rtclosure_covariant; eauto.
Qed.

Lemma tclosure_last : forall A (R : binary A) y x z,
  tclosure R x y -> 
  R y z -> 
  tclosure R x z.
Proof using.
  inversion 1; intros; subst.
  eauto using rtclosure_last with tclosure.
Qed.

(* If a relation is symmetric, then so is its transitive closure. *)

Lemma sym_rtclosure : forall A (R : binary A),
  sym R ->
  sym (rtclosure R).
Proof using.
  unfold sym. induction 2; eauto using rtclosure_last with rtclosure.
Qed.

Lemma sym_tclosure : forall A (R : binary A),
  sym R ->
  sym (tclosure R).
Proof using.
  unfold sym. inversion 2; subst.
  eapply tclosure_rtclosure_step.
  eapply sym_rtclosure; eauto.
  eauto.
Qed.

Lemma sclosure_rel_incl_stclosure : forall A (R : binary A),
  rel_incl (sclosure R) (stclosure R).
Proof using.
  unfold rel_incl. inversion 1; eauto with stclosure.
Qed.

Lemma tclosure_rel_incl_stclosure : forall A (R1 R2 : binary A),
  rel_incl R1 (stclosure R2) ->
  rel_incl (tclosure R1) (stclosure R2).
Proof using.
  introv H M. induction M using tclosure_ind_trans.
  applys* H.
  applys* stclosure_trans.
Qed.

Lemma stclosure_is_tclosure_sclosure : forall A (R : binary A),
  stclosure R = tclosure (sclosure R).
Proof using.
  extens. intros x y. split.
  { gen x y. induction 1.
    { eauto with tclosure sclosure rtclosure. }
    { eapply sym_tclosure. eapply sym_sclosure. eauto. }
    { eapply tclosure_trans; eauto. }
  }
  { intros.
    eapply tclosure_rel_incl_stclosure; [ | eassumption ].
    eapply sclosure_rel_incl_stclosure. }
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Comparison between a relation and a function *)

(** [fun_in_rel f R] asserts that input-output pairs of [f] are 
    included in the relation [R]. *)

Definition fun_in_rel A B (f:A->B) (R:A->B->Prop), :=
  forall x, R x (f x).

(** [rel_in_fun R f] asserts that input-output pairs of [R] 
    are input-output for [f]. *)

Definition rel_in_fun A B  (R:A->B->Prop) (f:A->B) :=
  forall x y, R x y -> y = f x.

(** The relation built from a function [f] is included in a relation  
    [R] iff the function [f] is included in [R] *)

Lemma rel_incl_rel_fun_iff_fun_in_rel : forall A B (f:A->B) (R:A->B->Prop),
  rel_incl (rel_fun f) R <-> fun_in_rel f R.
Proof.
  intros f R.
  unfold rel_fun, fun_in_rel. iff H; intros x; specializes H x.
    applys* H.
    intros y Hy. subst~.
Qed.

(* If the relation [R] is functional and if [f] is included in [R],
   then [R] is included in [f], i.e., they coincide. *)

Lemma rel_in_fun_from_fun_in_rel_functional : forall A B (f:A->B) (R:A->B->Prop),
  fun_in_rel f R ->
  functional R ->
  rel_in_fun R f.
Proof using.
  introv h1 h2. intros a b H. forwards M: h1 a. forwards*: h2 H M.
Qed.

(* TODO: [fun_in_rel f R] implies [defined R]
         [rel_in_fun R f] implies [functional R] *)


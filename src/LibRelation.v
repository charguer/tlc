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
(** * Properties of relations *)

(* ---------------------------------------------------------------------- *)
(** ** Reflexivity *)

Definition refl A (R:binary A) :=
  forall x, R x x.

Section Refl.
Variable (A : Type).
Implicit Types R : binary A.

Lemma refl_inv : forall x y R,
  refl R -> 
  x = y ->
  R x y.
Proof using. intros_all. subst~. Qed.

End Refl.


(* ---------------------------------------------------------------------- *)
(** ** Irreflexivity *)

Definition irrefl A (R:binary A) :=
  forall x, ~ (R x x).

Section Irrefl.
Variable (A : Type).
Implicit Types R : binary A.

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

End Irrefl.


(* ---------------------------------------------------------------------- *)
(** ** Symmetry *)

Definition sym A (R:binary A) :=
  forall x y, R x y -> R y x.

Section Sym.
Variable (A : Type).
Implicit Types R : binary A.

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

End Sym.


(* ---------------------------------------------------------------------- *)
(** ** Asymmetry *)

Definition asym A (R:binary A) :=
  forall x y, R x y -> ~ R y x.

Section Asym.
Variable (A : Type).
Implicit Types R : binary A.

Lemma asym_inv : forall x y R,
  asym R -> 
  R x y -> 
  R y x ->
  False.
Proof using. introv H M1 M2. apply* H. Qed.

End Asym.


(* ---------------------------------------------------------------------- *)
(** ** Antisymmetry *)

Definition antisym A (R:binary A) :=
  forall x y, R x y -> R y x -> x = y.

Section Antisym.
Variable (A : Type).
Implicit Types R : binary A.

Lemma antisym_inv : forall x y R,
  antisym R -> 
  R x y -> 
  R y x -> 
  x <> y -> 
  False.
Proof using. intros_all*. Qed.

End Antisym.


(* ---------------------------------------------------------------------- *)
(** ** Antisymmetry with respect to an equivalence relation *)

Definition antisym_wrt A (E:binary A) R :=
  forall x y, R x y -> R y x -> E x y.

(* LATER: lemmas *)


(* ---------------------------------------------------------------------- *)
(** ** Transitivity *)

Definition trans A (R:binary A) :=
  forall y x z, R x y -> R y z -> R x z.


Section Trans.
Variable (A : Type).
Implicit Types R : binary A.

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

(** [trans] + [sym] *)

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

End Trans.

Arguments trans_inv [A] y [x] [z] [R].
Arguments trans_inv_swap [A] y [x] [z] [R].
Arguments trans_sym_rr [A] y [x] [z] [R].
Arguments trans_sym_lr [A] y [x] [z] [R].
Arguments trans_sym_rl [A] y [x] [z] [R].


(* ---------------------------------------------------------------------- *)
(** ** Equivalence relation *)

Record equiv A (R:binary A) :=
 { equiv_refl : refl R;
   equiv_sym : sym R;
   equiv_trans : trans R }.

Section Equiv.
Variable (A : Type).
Implicit Types R : binary A.

(** Equality is an equivalence relation *)

Lemma equiv_eq : forall A, 
  equiv (@eq A).
Proof using. intros. constructor; intros_all; subst~. Qed.

End Equiv.


(* ---------------------------------------------------------------------- *)
(** ** Inclusion *)

(* LATER: see also typeclass [incl] *)

Definition rel_incl A B (R1 R2:A->B->Prop) :=
  forall x y, R1 x y -> R2 x y.

Section Incl.
Variable (A : Type).
Implicit Types R : binary A.

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

End Incl.


(* ---------------------------------------------------------------------- *)
(** ** Totality *)

Definition total A (R:binary A) :=
  forall x y, R x y \/ R y x.

Section Total.
Variable (A : Type).
Implicit Types R : binary A.

Lemma total_inv : forall x y R,
  total R -> 
  R x y \/ R y x.
Proof using. introv H. apply* H. Qed.

Lemma total_inv_not_l : forall x y R,
  total R -> 
  ~ R x y ->
  R y x.
Proof using. introv H N. destruct* (H x y). Qed.

Lemma total_inv_not_r : forall x y R,
  total R -> 
  ~ R y x ->
  R x y.
Proof using. introv H N. destruct* (H x y). Qed.

End Total.


(* ---------------------------------------------------------------------- *)
(** ** Definedness *)

Definition defined A B (R:A->B->Prop) :=
  forall x, exists y, R x y.

Section Defined.
Variable (A : Type).
Implicit Types R : binary A.

Lemma defined_inv : forall x R,
  defined R -> 
  exists y, R x y.
Proof using. introv H. apply* H. Qed.

Lemma defined_inv_not : forall x R,
  defined R -> 
  (forall y, ~ R x y) ->
  False.
Proof using. introv H N. forwards* (?&?): H. Qed.

End Defined.


(* ---------------------------------------------------------------------- *)
(** ** Functionality *)

Definition functional A B (R:A->B->Prop) :=
  forall x y z, R x y -> R x z -> y = z.

Section Functional.
Variable (A : Type).
Implicit Types R : binary A.

(* TODO: define a tactic "functional_exploit R" that looks for two distinct
   assumptions in the goal of the form [R ?x ?y] and produces [functional R]
   as subgoal, and provides the equality [?y1 = ?y2]. *)

Lemma functional_inv : forall x y z R,
  functional R -> 
  R x y -> 
  R x z -> 
  y = z.
Proof using. introv H N1 N2. apply* H. Qed.

End Functional.


(* ---------------------------------------------------------------------- *)
(** ** Criteria for equality *)

Section Equal.
Variable (A : Type).
Implicit Types R : binary A.

(** If [R1] is defined, [R2] is functional, and [R1] is a subset of [R2],
    then [R1] equals [R2]. In that case, [R1] and [R2] represent the graph
    of a total function. *)

Lemma eq_from_incl_defined_functional : forall R1 R2,
  rel_incl R1 R2 ->
  defined R1 ->
  functional R2 ->
  R1 = R2.
Proof using.
  introv Hincl Hdef Hfun. extens. intros x y. iff M.
  { eauto. }
  { forwards (w'&M1): Hdef x.
    forwards M2: Hincl M1.
    forwards: Hfun M M2. subst*. }
Qed.

End Equal.


(* ********************************************************************** *)
(** * Basic constructions *)

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

(* ---------------------------------------------------------------------- *)
(** ** The empty relation *)

(* LATER: see also typeclass [empty] *)

Definition empty A : binary A :=
  fun x y => False.

Section Empty.
Variable (A : Type).
Implicit Types x y : A.

Lemma empty_eq : forall x y,
  empty x y = False.
Proof using. auto. Qed.

Lemma empty_inv : forall x y,
  empty x y ->
  False.
Proof using. auto. Qed.

Lemma functional_empty : 
  functional (@empty A).
Proof using. unfolds* empty, functional. Qed.

End Empty.


(* ---------------------------------------------------------------------- *)
(** ** Union of two relations  *)

(* LATER: see also typeclass [union] *)

Definition union A (R1 R2:binary A) : binary A :=
  fun x y => R1 x y \/ R2 x y.

Section Union.
Variable (A : Type).
Implicit Types R : binary A.

Lemma union_l : forall R1 R2 x y,
  R1 x y ->
  union R1 R2 x y.
Proof using. unfold union. eauto. Qed.

Lemma union_r : forall R1 R2 x y,
  R2 x y ->
  union R1 R2 x y.
Proof using. unfold union. eauto. Qed.

Lemma rel_incl_union_l : forall R1 R2,
  rel_incl R1 (union R1 R2).
Proof using. unfold rel_incl, union. eauto. Qed.

Lemma rel_incl_union_r : forall R1 R2,
  rel_incl R2 (union R1 R2).
Proof using. unfold rel_incl, union. eauto. Qed.

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

(** Union is functional provided disjoint domains *)
Lemma functional_union : forall R1 R2,
  functional R1 ->
  functional R2 ->
  (forall x y z, R1 x y -> R2 x z -> False) ->
  functional (union R1 R2).
Proof using.
  intros. unfold union. intros x y z Hxy Hxz.
  destruct Hxy; destruct Hxz; auto_false*.
Qed.

(* TODO: generic definition of covariant? *)
Lemma covariant_union : forall R1 R2 S1 S2,
  rel_incl R1 S1 ->
  rel_incl R2 S2 ->
  rel_incl (union R1 R2) (union S1 S2).
Proof using. unfold rel_incl, union. autos*. Qed.

End Union.


(* ---------------------------------------------------------------------- *)
(** ** Intersection of two relations  *)

(* LATER: see also typeclass [inter] *)

Definition inter A (R1 R2:binary A) : binary A :=
  fun x y => R1 x y /\ R2 x y.

(* LATER: add lemmas *)


(* ---------------------------------------------------------------------- *)
(** ** Complement of a relation *)

Definition compl A (R:binary A) : binary A :=
  fun x y => ~ R y x.

(* LATER: add lemmas *)


(* ---------------------------------------------------------------------- *)
(** ** Inverse of a relation *)

Definition inverse A (R:binary A) : binary A :=
  fun x y => R y x.

Section Inverse.
Variable (A : Type).
Implicit Types R : binary A.

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

End Inverse.


(* ---------------------------------------------------------------------- *)
(** ** [preimage] *)

(** Preimage, a.k.a. inverse image *)

Definition rel_preimage (A B:Type) (R:binary B) (f:A->B) : binary A :=
  fun x y => R (f x) (f y).

(* TODO: lemams *)


(* ---------------------------------------------------------------------- *)
(** ** [rel_seq] *)

(** Composition of two relations, usually written [R1; R2]. *)

Definition rel_seq (A B C:Type) (R1:A->B->Prop) (R2:B->C->Prop) : A->C->Prop :=
  fun x z => exists y, R1 x y /\ R2 y z.

(** A relation [R] is functional if and only if [inverse R] composed
    with [R] is a subset of the diagonal relation [eq]. *)

Lemma functional_iff_seq_inverse_incl_eq : forall A (R:binary A),
  functional R <->
  rel_incl (rel_seq (inverse R) R) eq.
Proof using.
  unfold functional, rel_incl, rel_seq, inverse. iff; jauto.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Turning a function into a relation. *)

Definition rel_fun A B (f:A->B) :=
  fun x y => (y = f x).

Section Rel_fun.
Variable (A : Type).
Implicit Types R : binary A.

(* LATER: properties of [rel_fun] *)

End Rel_fun.



(* ********************************************************************** *)
(** * Products *)

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

(** Tactics *)

Tactic Notation "unfold_prod" :=
  unfold prod4, prod3, prod2.
Tactic Notation "unfolds_prod" :=
  unfold prod4, prod3, prod2 in *.

(** Equivalence *)

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

(* LATER: other lemmas *)


(* ---------------------------------------------------------------------- *)
(** ** Lexicographical product *)

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

(** Tactics *)

Tactic Notation "unfold_lexico" :=
  unfold lexico4, lexico3, lexico2.
Tactic Notation "unfolds_lexico" :=
  unfold lexico4, lexico3, lexico2 in *.

(** Elimination *)

Section Lexico.
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

End Lexico.

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

(* LATER: other lemmas *)



(* ********************************************************************** *)
(** * Closures *)

(* LATER: more lemmas about union and inter *)


(* ---------------------------------------------------------------------- *)
(** ** Reflexive closure  *)

Inductive rclosure (A:Type) (R:binary A) : binary A :=
  | rclosure_once : forall x y,
      R x y -> 
      rclosure R x y
  | rclosure_refl : forall x,
      rclosure R x x.

Section Rclosure.
Variable (A : Type).
Implicit Types R : binary A.
Hint Constructors rclosure.

(** Equivalent definition *)

Lemma rclosure_eq : forall R x y,  
  rclosure R x y = (R x y \/ x = y).
Proof using. extens. iff M; destruct M; subst*. Qed.

Lemma rclosure_inv : forall R x y,  
  rclosure R x y ->
  R x y \/ x = y.
Proof using. introv M; rewrite* rclosure_eq in M. Qed.

(** Properties *)

Lemma refl_rclosure : forall R,
  refl (rclosure R).
Proof using. unfolds* refl. Qed.

Lemma sym_rclosure : forall R,
  sym R ->
  sym (rclosure R).
Proof using. unfolds sym. introv M N. destruct* N. Qed.

Lemma antisym_rclosure : forall R,
  antisym R -> 
  antisym (rclosure R).
Proof using. 
  unfolds antisym. introv M N1 N2. 
  destruct N1; destruct N2; subst*.
Qed.

Lemma trans_rclosure : forall R,
  trans R ->
  trans (rclosure R).
Proof using.
  unfolds trans. introv H M1 M2.
  destruct M1; destruct M2; subst*.
Qed.

Lemma total_rclosure : forall R,
  total R -> 
  total (rclosure R).
Proof using. 
  unfolds total. introv H. intros x y. destruct* (H x y).
Qed.

Lemma rclosure_of_refl : forall R,
  refl R ->
  rclosure R = R.
Proof using.
  unfolds refl. introv H. extens. iff M.
  { destruct M; subst*. } { auto. }
Qed.

Lemma rclosure_inverse_eq : forall R,
  rclosure (inverse R) = inverse (rclosure R).
Proof using. unfold inverse. extens. iff M; destruct* M. Qed.

(** Constructors *)

Lemma rclosure_trans_l : forall y x z R,
  trans R -> 
  rclosure R x y -> 
  R y z -> 
  rclosure R x z.
Proof using. introv T M N. rewrite rclosure_eq in *. destruct M; subst*. Qed.

Lemma rclosure_trans_r : forall y x z R,
  trans R -> 
  R x y -> 
  rclosure R y z -> 
  rclosure R x z.
Proof using. introv T M N. rewrite rclosure_eq in *. destruct N; subst*. Qed.

Lemma trans_rclosure_l : forall y x z R,
  trans R -> 
  rclosure R x y -> 
  R y z -> 
  R x z.
Proof using. introv T M H. rewrite rclosure_eq in *. destruct M; subst*. Qed.

Lemma trans_rclosure_r : forall y x z R,
  trans R -> 
  R x y -> 
  rclosure R y z -> 
  R x z.
Proof using. introv T M N. rewrite rclosure_eq in *. destruct N; subst*. Qed.

(** Negation *)

Lemma not_rclosure_inv : forall R x y,
  ~ rclosure R x y ->
  ~ R x y /\ x <> y.
Proof using. introv M. rewrite* rclosure_eq in M. Qed.

Lemma not_rclosure_inv_rel : forall R x y,
  ~ rclosure R x y ->
  ~ R x y.
Proof using. introv M. rewrite* rclosure_eq in M. Qed.

Lemma not_rclosure_inv_neq : forall R x y,
  ~ rclosure R x y ->
  x <> y.
Proof using. introv M. rewrite* rclosure_eq in M. Qed.

(** Inclusions *)

Lemma rel_incl_rclosure : forall R,
  rel_incl R (rclosure R).
Proof using. unfolds* rel_incl. Qed.

Lemma covariant_rclosure : forall R1 R2,
  rel_incl R1 R2 ->
  rel_incl (rclosure R1) (rclosure R2).
Proof using. introv H M. destruct* M. Qed.

Lemma rel_incl_rclosure_rclosure : forall R1 R2,
  rel_incl R1 (rclosure R2) ->
  rel_incl (rclosure R1) (rclosure R2).
Proof using. introv H M. destruct* M. Qed.

End Rclosure.

Hint Constructors rclosure : rclosure.
(* LATER: here and later, add more hints *)


(* ---------------------------------------------------------------------- *)
(** ** Symmetric closure  *)

Inductive sclosure (A:Type) (R:binary A) : binary A :=
  | sclosure_once : forall x y,
      R x y -> 
      sclosure R x y
  | sclosure_sym : forall x y,
      sclosure R y x ->
      sclosure R x y.

Section Sclosure.
Variable (A : Type).
Implicit Types R : binary A.
Hint Constructors sclosure.

(** Equivalent definition *)

Lemma sclosure_eq : forall R x y,  
  sclosure R x y = (R x y \/ R y x).
Proof using.
  extens. iff M.
  { induction* M. } 
  { destruct M; subst*. }
Qed.

Lemma sclosure_inv : forall R x y,  
  sclosure R x y ->
  R x y \/ R y x.
Proof using. introv M; rewrite* sclosure_eq in M. Qed.

(** Properties *)

Lemma refl_sclosure : forall R,
  refl R ->
  refl (sclosure R).
Proof using. unfolds* refl. Qed.

Lemma sym_sclosure : forall R,
  sym (sclosure R).
Proof using. unfolds sym. introv N. destruct* N. Qed.

Lemma total_sclosure : forall R,
  total R ->
  total (sclosure R).
Proof using. 
  unfolds total. introv H. intros x y. destruct* (H x y).
Qed.

Lemma sclosure_of_sym : forall R,
  sym R ->
  sclosure R = R.
Proof using.
  unfolds sym. introv H. extens. intros. rewrite sclosure_eq.
  iff M. { destruct M; subst*. } { auto. }
Qed.

Lemma sclosure_inverse_eq : forall R,
  sclosure (inverse R) = sclosure R.
Proof using. 
  unfolds inverse. extens. intros. do 2 rewrite sclosure_eq. autos*.
Qed.

(** Negation *)

Lemma not_sclosure_inv : forall R x y,
  ~ sclosure R x y ->
  ~ R x y /\ ~ R y x.
Proof using. introv M. rewrite* sclosure_eq in M. Qed.

Lemma not_sclosure_inv_l : forall R x y,
  ~ sclosure R x y ->
  R x y ->
  False.
Proof using. introv M. rewrite* sclosure_eq in M. Qed.

Lemma not_sclosure_inv_r : forall R x y,
  ~ sclosure R x y ->
  R y x ->
  False.
Proof using. introv M. rewrite* sclosure_eq in M. Qed.

(** Inclusions *)

Lemma rel_incl_sclosure : forall R,
  rel_incl R (sclosure R).
Proof using. unfolds* rel_incl. Qed.

Lemma rel_incl_inverse_sclosure : forall R,
  rel_incl (inverse R) (sclosure R).
Proof using. unfolds* rel_incl, inverse. Qed.

Lemma covariant_sclosure : forall R1 R2,
  rel_incl R1 R2 ->
  rel_incl (sclosure R1) (sclosure R2).
Proof using. introv H M. induction* M. Qed.

Lemma rel_incl_sclosure_sclosure : forall R1 R2,
  rel_incl R1 (sclosure R2) ->
  rel_incl (sclosure R1) (sclosure R2).
Proof using. introv H M. induction* M. Qed.

End Sclosure.

Hint Constructors sclosure : sclosure.


(* ---------------------------------------------------------------------- *)
(** ** Reflexive-symmetric closure  *)

Inductive rsclosure (A:Type) (R:binary A) : binary A :=
  | rsclosure_once : forall x y,
      R x y -> 
      rsclosure R x y
  | rsclosure_refl : forall x,
      rsclosure R x x
  | rsclosure_sym : forall x y,
      rsclosure R x y ->
      rsclosure R y x.

Section Rsclosure.
Variable (A : Type).
Implicit Types R : binary A.
Hint Constructors rsclosure.

(** Equivalent definition *)

Lemma rsclosure_eq : forall R x y,  
  rsclosure R x y = (R x y \/ R y x \/ x = y).
Proof using.
  extens. iff M.
  { induction* M. } 
  { destruct M as [M|[M|M]]; subst*. }
Qed.

Lemma rsclosure_inv : forall R x y,  
  rsclosure R x y ->
  R x y \/ R y x \/ x = y.
Proof using. introv M; rewrite* rsclosure_eq in M. Qed.

(** Properties *)

Lemma refl_rsclosure : forall R,
  refl (rsclosure R).
Proof using. unfolds* refl. Qed.

Lemma sym_rsclosure : forall R,
  sym (rsclosure R).
Proof using. unfolds sym. introv N. destruct* N. Qed.

Lemma total_rsclosure : forall R,
  total R ->
  total (rsclosure R).
Proof using.
  unfolds total. introv H. intros x y. destruct* (H x y).
Qed.

Lemma rsclosure_inverse_eq : forall R,
  rsclosure (inverse R) = rsclosure R.
Proof using.
  unfold inverse. extens. intros. do 2 rewrite rsclosure_eq. autos*.
Qed.

(** Negation *)

Lemma not_rsclosure_inv : forall R x y,
  ~ rsclosure R x y ->
  ~ R x y /\ ~ R y x /\ ~ x = y.
Proof using. introv M. rewrite* rsclosure_eq in M. Qed.

Lemma not_rsclosure_inv_l : forall R x y,
  ~ rsclosure R x y ->
  R x y ->
  False.
Proof using. introv M. rewrite* rsclosure_eq in M. Qed.

Lemma not_rsclosure_inv_r : forall R x y,
  ~ rsclosure R x y ->
  R y x ->
  False.
Proof using. introv M. rewrite* rsclosure_eq in M. Qed.

Lemma not_rsclosure_inv_neq : forall R x y,
  ~ rsclosure R x y ->
  x <> y.
Proof using. introv M. rewrite* rsclosure_eq in M. Qed.

(** Inclusions *)

Lemma rel_incl_rsclosure : forall R,
  rel_incl R (rsclosure R).
Proof using. unfolds* rel_incl. Qed.

Lemma rel_incl_inverse_rsclosure : forall R,
  rel_incl (inverse R) (rsclosure R).
Proof using. unfolds* rel_incl, inverse. Qed.

Lemma covariant_rsclosure : forall R1 R2,
  rel_incl R1 R2 ->
  rel_incl (rsclosure R1) (rsclosure R2).
Proof using. introv H M. induction* M. Qed.

Lemma rel_incl_rsclosure_rsclosure : forall R1 R2,
  rel_incl R1 (rsclosure R2) ->
  rel_incl (rsclosure R1) (rsclosure R2).
Proof using. introv H M. induction* M. Qed.

End Rsclosure.

Hint Constructors rsclosure : rsclosure.


(* ---------------------------------------------------------------------- *)
(** ** Transitive closure ( R+ ), defined as [R \o R*] *)

Inductive tclosure (A:Type) (R:binary A) : binary A :=
  | tclosure_once : forall x y,
      R x y -> 
      tclosure R x y
  | tclosure_trans : forall y x z,
      tclosure R x y -> 
      tclosure R y z -> 
      tclosure R x z.

Section Tclosure.
Variable (A : Type).
Implicit Types R : binary A.
Hint Constructors tclosure.

(** Properties *)

Lemma refl_tclosure : forall R,
  refl R ->
  refl (tclosure R).
Proof using. unfolds* refl. Qed.

Lemma sym_tclosure : forall R,
  sym R ->
  sym (tclosure R).
Proof using. unfolds sym. introv H N. induction* N. Qed.

Lemma trans_tclosure : forall R,
  trans (tclosure R).
Proof using. unfolds* trans. Qed.

Lemma total_tclosure : forall R,
  total R ->
  total (tclosure R).
Proof using. 
  unfolds total. introv H. intros x y. destruct* (H x y).
Qed.

Lemma tclosure_of_trans : forall R,
  trans R ->
  tclosure R = R.
Proof using.
  unfolds trans. introv H. extens. iff M.
  { induction M; subst*. }
  { auto. }
Qed.

Lemma tclosure_inverse_eq : forall R,
  tclosure (inverse R) = inverse (tclosure R).
Proof using. 
  unfolds inverse. extens. intros x y. iff M; induction* M. 
Qed.

(** Constructors *)

Lemma tclosure_l : forall R y x z,
  R x y -> 
  tclosure R y z -> 
  tclosure R x z.
Proof using. autos*. Qed.

Lemma tclosure_r : forall R y x z,
  tclosure R x y -> 
  R y z -> 
  tclosure R x z.
Proof using. autos*. Qed.

(** Inclusions *)

Lemma rel_incl_tclosure : forall R,
  rel_incl R (tclosure R).
Proof using. unfolds* rel_incl. Qed.

Lemma covariant_tclosure : forall A (R1 R2 : binary A),
  rel_incl R1 R2 ->
  rel_incl (tclosure R1) (tclosure R2).
Proof using. introv H M. induction* M. Qed.

Lemma rel_incl_tclosure_tclosure : forall R1 R2,
  rel_incl R1 (tclosure R2) ->
  rel_incl (tclosure R1) (tclosure R2).
Proof using. introv H M. induction* M. Qed.

(** Induction principle with steps at head or tail *)

Section Ind.

Inductive tclosure'l (A:Type) (R:binary A) : binary A :=
  | tclosure'l_once : forall x y,
      R x y -> 
      tclosure'l R x y
  | tclosure'l_step : forall y x z,
      R x y -> 
      tclosure'l R y z -> 
      tclosure'l R x z.

Lemma tclosure'l_trans : forall R,
  trans (tclosure'l R).
Proof using.
  Hint Constructors tclosure'l.
  intros R y x z M1. gen z. induction M1; introv M2; autos*.
Qed.  

Lemma tclosure_eq_tclosure'l : forall R,
  tclosure R = tclosure'l R.
  (* LATER: tclosure'l = tclosure. *)
Proof using.
  extens. intros x y. iff M.  
  { induction* M. applys* tclosure'l_trans y. }
  { induction* M. }
Qed.

Lemma tclosure_ind_l : forall R (P : A -> A -> Prop),
  (forall x y, R x y -> P x y) ->
  (forall y x z, R x y -> tclosure R y z -> P y z -> P x z) ->
  (forall x y, tclosure R x y -> P x y).
Proof.
  introv H1 H2 M. rewrite tclosure_eq_tclosure'l in *. induction* M.
Qed.

Inductive tclosure'r (A:Type) (R:binary A) : binary A :=
  | tclosure'r_once : forall x y,
      R x y -> 
      tclosure'r R x y
  | tclosure'r_step : forall y x z,
      tclosure'r R x y -> 
      R y z ->
      tclosure'r R x z.

Lemma tclosure'r_trans : forall R,
  trans (tclosure'r R).
Proof using.
  Hint Constructors tclosure'r.
  intros R y x z M1 M2. gen x. induction M2; introv M1; autos*.
Qed.  

Lemma tclosure_eq_tclosure'r : forall R,
  tclosure R = tclosure'r R.
  (* LATER: tclosure'l = tclosure. *)
Proof using.
  extens. intros x y. iff M.  
  { induction* M. applys* tclosure'r_trans y. }
  { induction* M. }
Qed.

Lemma tclosure_ind_r : forall R (P : A -> A -> Prop),
  (forall x y, R x y -> P x y) ->
  (forall y x z, tclosure R x y -> P x y -> R y z -> P x z) ->
  (forall x y, tclosure R x y -> P x y).
Proof.
  introv H1 H2 M. rewrite tclosure_eq_tclosure'r in *. induction* M.
Qed.

(* LATER: can these induction principles be proved directly? *)

End Ind.

(** Inversion principle with steps at head or tail *)

Lemma tclosure_inv_l : forall R x z,
  tclosure R x z ->
  (R x z) \/ (exists y, R x y /\ tclosure R y z).
Proof. intros R. applys* tclosure_ind_l. Qed.

Lemma tclosure_inv_r : forall R x z,
  tclosure R x z ->
  (R x z) \/ (exists y, tclosure R x y /\ R y z).
Proof. intros R. applys* tclosure_ind_r. Qed.

End Tclosure.

Hint Resolve tclosure_once tclosure_l tclosure_r
  : rtclosure.


(* ---------------------------------------------------------------------- *)
(** ** Reflexive-transitive closure ( R* ) *)

Inductive rtclosure (A:Type) (R:binary A) : binary A :=
  | rtclosure_once : forall x y,
      R x y ->
      rtclosure R x y
  | rtclosure_refl : forall x,
      rtclosure R x x
  | rtclosure_trans : forall y x z,
      rtclosure R x y -> 
      rtclosure R y z -> 
      rtclosure R x z.

Section Rtclosure.
Variable (A : Type).
Implicit Types R : binary A.
Hint Constructors rtclosure.

(** Properties *)

Lemma refl_rtclosure : forall R,
  refl (rtclosure R).
Proof using. unfolds* refl. Qed.

Lemma sym_rtclosure : forall R,
  sym R ->
  sym (rtclosure R).
Proof using. unfolds sym. introv M N. induction* N. Qed.

Lemma trans_rtclosure : forall R,
  trans (rtclosure R).
Proof using. unfolds* trans. Qed.

Lemma total_rtclosure : forall R,
  total R ->
  total (rtclosure R).
Proof using. 
  unfolds total. introv H. intros x y. destruct* (H x y).
Qed.

Lemma tclosure_of_refl_trans : forall R,
  refl R ->
  trans R ->
  rtclosure R = R.
Proof using.
  unfolds refl, trans. introv H1 H2. extens. iff M.
  { induction M; subst*. }
  { autos*. }
Qed.

Lemma rtclosure_inverse_eq : forall R,
  rtclosure (inverse R) = inverse (rtclosure R).
Proof using. unfold inverse. extens. iff M; induction* M. Qed.

(** Constructors *)

Lemma rtclosure_l : forall R y x z,
  R x y -> 
  rtclosure R y z -> 
  rtclosure R x z.
Proof using. autos*. Qed.

Lemma rtclosure_r : forall R y x z,
  rtclosure R x y -> 
  R y z -> 
  rtclosure R x z.
Proof using. autos*. Qed.

(* Same as above, reformulated to make [eauto] faster *)
Lemma rtclosure_r' : forall R y x z,
  R y z -> 
  rtclosure R x y -> 
  rtclosure R x z.
Proof using. autos*. Qed.

(** Inclusion *)

Lemma rel_incl_rtclosure : forall R,
  rel_incl R (rtclosure R).
Proof using. unfolds* rel_incl. Qed.

Lemma covariant_rtclosure : forall R1 R2,
  rel_incl R1 R2 ->
  rel_incl (rtclosure R1) (rtclosure R2).
Proof using. unfolds rel_incl. introv H M. induction* M. Qed.

(* TODO: find better name for this one and similar *)
Lemma rel_incl_rtclosure_rtclosure : forall R1 R2,
  rel_incl R1 (rtclosure R2) ->
  rel_incl (rtclosure R1) (rtclosure R2).
Proof using. unfolds rel_incl. introv H M. induction* M. Qed.

Lemma rel_incl_union_rtclosure : forall R1 R2,
  rel_incl (union (rtclosure R1) (rtclosure R2))
           (rtclosure (union R1 R2)).
Proof using.
  hint rel_incl_union_l, rel_incl_union_r. introv [M|M].
  { applys* covariant_rtclosure R1. }
  { applys* covariant_rtclosure R2. }
Qed.

(** Negation *)

Lemma not_rtclosure_inv_neq : forall R x y,
  ~ rtclosure R x y ->
  x <> y.
Proof using. introv M E. subst. induction* M. Qed.

(** Induction principle with steps at head or tail *)

Section Ind.

Inductive rtclosure'l (A:Type) (R:binary A) : binary A :=
  | rtclosure'l_refl : forall x,
      rtclosure'l R x x
  | rtclosure'l_step : forall y x z,
      R x y -> 
      rtclosure'l R y z -> 
      rtclosure'l R x z.

Lemma rtclosure'l_trans : forall R,
  trans (rtclosure'l R).
Proof using.
  Hint Constructors rtclosure'l.
  intros R y x z M1. gen z. induction M1; introv M2; autos*.
Qed.  

Lemma rtclosure_eq_rtclosure'l : forall R,
  rtclosure R = rtclosure'l R.
  (* LATER: tclosure'l = tclosure. *)
Proof using.
  extens. intros x y. iff M.  
  { induction* M. applys* rtclosure'l_trans y. }
  { induction* M. }
Qed.

Lemma rtclosure_ind_l : forall R (P : A -> A -> Prop),
  (forall x, P x x) ->
  (forall y x z, R x y -> rtclosure R y z -> P y z -> P x z) ->
  (forall x y, rtclosure R x y -> P x y).
Proof.
  introv H1 H2 M. rewrite rtclosure_eq_rtclosure'l in *. induction* M.
Qed.

Inductive rtclosure'r (A:Type) (R:binary A) : binary A :=
  | rtclosure'r_refl : forall x,
      rtclosure'r R x x
  | rtclosure'r_step : forall y x z,
      rtclosure'r R x y -> 
      R y z ->
      rtclosure'r R x z.

Lemma rtclosure'r_trans : forall R,
  trans (rtclosure'r R).
Proof using.
  Hint Constructors rtclosure'r.
  intros R y x z M1 M2. gen x. induction M2; introv M1; autos*.
Qed.  

Lemma rtclosure_eq_rtclosure'r : forall R,
  rtclosure R = rtclosure'r R.
  (* LATER: tclosure'l = tclosure. *)
Proof using.
  extens. intros x y. iff M.  
  { induction* M. applys* rtclosure'r_trans y. }
  { induction* M. }
Qed.

Lemma rtclosure_ind_r : forall R (P : A -> A -> Prop),
  (forall x, P x x) ->
  (forall y x z, rtclosure R x y -> P x y -> R y z -> P x z) ->
  (forall x y, rtclosure R x y -> P x y).
Proof.
  introv H1 H2 M. rewrite rtclosure_eq_rtclosure'r in *. induction* M.
Qed.

End Ind.

(** Inversion principle with steps at head or tail *)

Lemma rtclosure_inv_l : forall R x z,
  rtclosure R x z ->
  (x = z) \/ (exists y, R x y /\ rtclosure R y z).
Proof. intros R. applys* rtclosure_ind_l. Qed.

Lemma rtclosure_inv_r : forall R x z,
  rtclosure R x z ->
  (x = z) \/ (exists y, rtclosure R x y /\ R y z).
Proof. intros R. applys* rtclosure_ind_r. Qed.

End Rtclosure.

Hint Resolve rtclosure_refl rtclosure_once 
  rtclosure_l rtclosure_r' : rtclosure.


(* ---------------------------------------------------------------------- *)
(** ** Symmetric-transitive closure *)

Inductive stclosure (A:Type) (R:binary A) : binary A :=
  | stclosure_once : forall x y,
      R x y -> 
      stclosure R x y
  | stclosure_sym : forall x y,
      stclosure R x y -> 
      stclosure R y x
  | stclosure_trans : forall y x z,
      stclosure R x y -> 
      stclosure R y z -> 
      stclosure R x z.

Section Stclosure.
Variable (A : Type).
Implicit Types R : binary A.
Hint Constructors stclosure.

(** Properties *)

Lemma refl_stclosure : forall R,
  refl R ->
  refl (stclosure R).
Proof using. unfolds* refl. Qed.

Lemma sym_stclosure : forall R,
  sym (stclosure R).
Proof using. unfolds sym. introv N. induction* N. Qed.

Lemma trans_stclosure : forall R,
  trans (stclosure R).
Proof using. unfolds* trans. Qed.

Lemma total_stclosure : forall R,
  total R ->
  total (stclosure R).
Proof using. 
  unfolds total. introv H. intros x y. destruct* (H x y).
Qed.

Lemma stclosure_of_sym_trans : forall R,
  sym R ->
  trans R ->
  rtclosure R = R.
Proof using.
  unfolds sym, trans. introv H1 H2. extens. iff M.
  { induction M; subst*. }
  { autos*. }
Qed.

Lemma stclosure_inverse_eq : forall R,
  stclosure (inverse R) = inverse (stclosure R).
Proof using. 
  unfolds inverse. extens. intros x y. iff M; induction* M. 
Qed.

(** Constructors *)

Lemma stclosure_l : forall R y x z,
  R x y -> 
  stclosure R y z -> 
  stclosure R x z.
Proof using. autos*. Qed.

Lemma stclosure_r : forall R y x z,
  stclosure R x y -> 
  R y z -> 
  stclosure R x z.
Proof using. autos*. Qed.

(** Inclusion *)

Lemma rel_incl_stclosure : forall R,
  rel_incl R (stclosure R).
Proof using. unfolds* rel_incl. Qed.

Lemma covariant_stclosure : forall R1 R2,
  rel_incl R1 R2 -> 
  rel_incl (stclosure R1) (stclosure R2).
Proof using. introv H M. induction* M. Qed.

Lemma rel_incl_stclosure_stclosure : forall R1 R2,
  rel_incl R1 (stclosure R2) ->
  rel_incl (stclosure R1) (stclosure R2).
Proof using. introv H M. induction* M. Qed.

End Stclosure.

Hint Constructors stclosure : stclosure.


(* ---------------------------------------------------------------------- *)
(** ** Reflexive-symmetric-transitive closure *)

Inductive rstclosure (A:Type) (R:binary A) : binary A :=
  | rstclosure_once : forall x y,
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

Section Rstclosure.
Variable (A : Type).
Implicit Types R : binary A.
Hint Constructors rstclosure.

(** Properties *)

Lemma refl_rstclosure : forall R,
  refl (rstclosure R).
Proof using. unfolds* refl. Qed.

Lemma sym_rstclosure : forall R,
  sym (rstclosure R).
Proof using. unfolds* sym. Qed.

Lemma trans_rstclosure : forall R,
  trans (rstclosure R).
Proof using. unfolds* trans. Qed.

Lemma total_rstclosure : forall R,
  total R ->
  total (rstclosure R).
Proof using. 
  unfolds total. introv H. intros x y. destruct* (H x y).
Qed.

Lemma rstclosure_of_refl_sym_trans : forall R,
  refl R ->
  sym R ->
  trans R ->
  rstclosure R = R.
Proof using.
  unfolds refl, sym, trans. introv H. extens. iff M.
  { induction M; subst*. }
  { auto. }
Qed.

Lemma rstclosure_inverse_eq : forall R,
  rstclosure (inverse R) = rstclosure R.
Proof using. 
  unfolds inverse. extens. intros x y. iff M; induction* M. 
Qed.

(** Constructors *)

Lemma rstclosure_l : forall R y x z,
  R x y -> 
  rstclosure R y z -> 
  rstclosure R x z.
Proof using. autos*. Qed.

Lemma rstclosure_r : forall R y x z,
  rstclosure R x y -> 
  R y z -> 
  rstclosure R x z.
Proof using. autos*. Qed.

(** Inclusion *)

Lemma rel_incl_rstclosure : forall R,
  rel_incl R (rstclosure R).
Proof using. unfolds* rel_incl. Qed.

Lemma rel_incl_inverse_rstclosure : forall R,
  rel_incl (inverse R) (rstclosure R).
Proof using. unfolds* rel_incl, inverse. Qed.

Lemma covariant_rstclosure : forall R1 R2,
  rel_incl R1 R2 ->
  rel_incl (rstclosure R1) (rstclosure R2).
Proof using. introv H M. induction* M. Qed.

Lemma rel_incl_rstclosure_rstclosure : forall R1 R2,
  rel_incl R1 (rstclosure R2) ->
  rel_incl (rstclosure R1) (rstclosure R2).
Proof using. introv H M. induction* M. Qed.

Lemma rel_incl_union_rstclosure : forall R1 R2,
  rel_incl (union (rstclosure R1) (rstclosure R2))
           (rstclosure (union R1 R2)).
Proof using.
  hint rel_incl_union_l, rel_incl_union_r. introv [M|M].
  { applys* covariant_rstclosure R1. }
  { applys* covariant_rstclosure R2. }
Qed.

End Rstclosure.

Hint Constructors rstclosure : rstclosure.


(* ---------------------------------------------------------------------- *)
(** ** Relationship between closures *)

Section ClosuresRel.
Variable (A : Type).
Implicit Types R : binary A.
Hint Constructors rtclosure rsclosure stclosure rstclosure.

(** [rclosure] to [rtclosure] *)

Lemma rtclosure_from_rclosure : forall R x y,
  rclosure R x y -> 
  rtclosure R x y.
Proof using. intros. destruct* H. Qed.

Lemma incl_rclosure_rtclosure : forall R,
  rel_incl (rclosure R) (rtclosure R).
Proof using. intros. applys* rtclosure_from_rclosure. Qed.

(** [tclosure] to [rtclosure] *)

Lemma rtclosure_from_tclosure : forall R x y,
  tclosure R x y -> 
  rtclosure R x y.
Proof using. intros. induction* H. Qed.

Lemma incl_tclosure_rtclosure : forall R,
  rel_incl (tclosure R) (rtclosure R).
Proof using. intros. applys* rtclosure_from_tclosure. Qed.

(** [rclosure] to [rsclosure] *)

Lemma rsclosure_from_rclosure : forall R x y,
  rclosure R x y -> 
  rsclosure R x y.
Proof using. intros. destruct* H. Qed.

Lemma incl_rclosure_rsclosure : forall R,
  rel_incl (rclosure R) (rsclosure R).
Proof using. intros. applys* rsclosure_from_rclosure. Qed.

(** [sclosure] to [rsclosure] *)

Lemma rsclosure_from_sclosure : forall R x y,
  sclosure R x y -> 
  rsclosure R x y.
Proof using. intros. destruct* H. Qed.

Lemma incl_sclosure_rsclosure : forall R,
  rel_incl (sclosure R) (rsclosure R).
Proof using. intros. applys* rsclosure_from_sclosure. Qed.

(** [sclosure] to [stclosure] *)

Lemma stclosure_from_sclosure : forall R x y,
  sclosure R x y -> 
  stclosure R x y.
Proof using. intros. induction* H. Qed.

Lemma incl_slosure_rsclosure : forall R,
  rel_incl (sclosure R) (stclosure R).
Proof using. intros. applys* stclosure_from_sclosure. Qed.

(** [tclosure] to [stclosure] *)

Lemma stclosure_from_tclosure : forall R x y,
  tclosure R x y -> 
  stclosure R x y.
Proof using. intros. induction* H. Qed.

Lemma incl_tclosure_stclosure : forall R,
  rel_incl (tclosure R) (stclosure R).
Proof using. intros. applys* stclosure_from_tclosure. Qed.

(** [rclosure] to [rstclosure] *)

Lemma rstclosure_from_rclosure : forall R x y,
  rclosure R x y -> 
  rstclosure R x y.
Proof using. intros. destruct* H. Qed.

Lemma incl_rclosure_rstclosure : forall R,
  rel_incl (rclosure R) (rstclosure R).
Proof using. intros. applys* rstclosure_from_rclosure. Qed.

(** [sclosure] to [rstclosure] *)

Lemma rstclosure_from_sclosure : forall R x y,
  sclosure R x y -> 
  rstclosure R x y.
Proof using. intros. induction* H. Qed.

Lemma incl_sclosure_rstclosure : forall R,
  rel_incl (sclosure R) (rstclosure R).
Proof using. intros. applys* rstclosure_from_sclosure. Qed.

(** [tclosure] to [tstclosure] *)

Lemma rstclosure_from_tclosure : forall R x y,
  tclosure R x y -> 
  rstclosure R x y.
Proof using. intros. induction* H. Qed.

Lemma incl_tclosure_rstclosure : forall R,
  rel_incl (tclosure R) (rstclosure R).
Proof using. intros. applys* rstclosure_from_tclosure. Qed.

(** [rsclosure] to [rstclosure] *)

Lemma rstclosure_from_rsclosure : forall R x y,
  rsclosure R x y -> 
  rstclosure R x y.
Proof using. intros. induction* H. Qed.

Lemma incl_rsclosure_rstclosure : forall R,
  rel_incl (rsclosure R) (rstclosure R).
Proof using. intros. applys* rstclosure_from_rsclosure. Qed.

(** [rtclosure] to [rstclosure] *)

Lemma rstclosure_from_rtclosure : forall R x y,
  rtclosure R x y -> 
  rstclosure R x y.
Proof using. intros. induction* H. Qed.

Lemma incl_rtclosure_rstclosure : forall R,
  rel_incl (rtclosure R) (rstclosure R).
Proof using. intros. applys* rstclosure_from_rtclosure. Qed.

(** [stclosure] to [rstclosure] *)

Lemma rstclosure_from_stclosure : forall R x y,
  stclosure R x y -> 
  rstclosure R x y.
Proof using. intros. induction* H. Qed.

Lemma incl_stclosure_rstclosure : forall R,
  rel_incl (stclosure R) (rstclosure R).
Proof using. intros. applys* rstclosure_from_stclosure. Qed.

End ClosuresRel.


(* ---------------------------------------------------------------------- *)
(** ** Iterated closures *)

Section IterClosures.
Variable (A : Type).
Implicit Types R : binary A.
Hint Constructors rclosure sclosure tclosure 
  rtclosure rsclosure stclosure rstclosure.
Hint Resolve sym_tclosure sym_sclosure sym_rclosure
  sym_rtclosure sym_rsclosure sym_rtclosure sym_rstclosure.

Lemma rclosure_sclosure_eq_rsclosure : forall R,
  rclosure (sclosure R) = rsclosure R.
Proof using.
  extens. intros x y. iff M.
  { destruct* M. { applys* rsclosure_from_sclosure. } }
  { induction* M. { applys* sym_inv. } }
Qed.

Lemma sclosure_rclosure_eq_rsclosure : forall R,
  sclosure (rclosure R) = rsclosure R.
Proof using.
  extens. intros x y. iff M.
  { induction* M. { applys* rsclosure_from_rclosure. } }
  { induction* M. }
Qed.

Lemma rclosure_tclosure_eq_rtclosure : forall R,
  rclosure (tclosure R) = rtclosure R.
Proof using.
  extens. intros x y. iff M.
  { induction* M. { applys* rtclosure_from_tclosure. } }
  { induction* M. { destruct IHM1; destruct IHM2; autos*. } }
Qed.

Lemma tclosure_rclosure_eq_rtclosure : forall R,
  tclosure (rclosure R) = rtclosure R.
Proof using.
  extens. intros x y. iff M.
  { induction* M. { applys* rtclosure_from_rclosure. } }
  { induction* M. }
Qed.

Lemma tclosure_sclosure_eq_stclosure : forall R,
  tclosure (sclosure R) = stclosure R.
Proof using.
  extens. intros x y. iff M.
  { induction* M. { applys* stclosure_from_sclosure. } }
  { induction* M. { applys* sym_inv. } }
Qed.

Lemma rclosure_stclosure_eq_rstclosure : forall R,
  rclosure (stclosure R) = rstclosure R.
Proof using.
  extens. intros x y. iff M.
  { induction* M. { applys* rstclosure_from_stclosure. } }
  { induction* M.
    { destruct IHM; autos*. }
    { destruct IHM1; destruct IHM2; autos*. } }
Qed.

Lemma stclosure_rclosure_eq_rstclosure : forall R,
  stclosure (rclosure R) = rstclosure R.
Proof using.
  extens. intros x y. iff M.
  { induction* M. { applys* rstclosure_from_rclosure. } }
  { induction* M. }
Qed.

Lemma rtclosure_sclosure_eq_rstclosure : forall R,
  rtclosure (sclosure R) = rstclosure R.
Proof using.
  extens. intros x y. iff M.
  { induction* M. { applys* rstclosure_from_sclosure. } }
  { induction* M. { applys* sym_inv. } }
Qed.

Lemma tclosure_rsclosure_eq_rstclosure : forall R,
  tclosure (rsclosure R) = rstclosure R.
Proof using.
  extens. intros x y. iff M.
  { induction* M. { applys* rstclosure_from_rsclosure. } }
  { induction* M. { applys* sym_inv. } }
Qed.

End IterClosures.


(* ---------------------------------------------------------------------- *)
(** ** Equivalent closures *)

Section EquivClosures.
Variable (A : Type).
Implicit Types R : binary A.

Lemma stclosure_eq_rstclosure_from_refl : forall R,
  refl R ->
  stclosure R = rstclosure R.
Proof using.
  intros. eapply binary_extensional. intros x y.
  split; eauto using stclosure_rstclosure.
  gen x y. induction 1; eauto with stclosure.
Qed.

Lemma rel_incl_tclosure_stclosure : forall R1 R2,
  rel_incl R1 (stclosure R2) ->
  rel_incl (tclosure R1) (stclosure R2).
Proof using.
  introv H M. induction M using tclosure_ind_trans.
  applys* H.
  applys* stclosure_trans.
Qed.

(* LATER: may lemmas like the two above *) 

End EquivClosures.


(* ---------------------------------------------------------------------- *)
(** ** Mixed transitivity between closures *)

Section MixedClosures.
Variable (A : Type).
Implicit Types R : binary A.
Hint Constructors rstclosure.

Lemma tclosure_from_rtclosure_l : forall R x y z,
  rtclosure R x y -> 
  R y z -> 
  tclosure R x z.
Proof using. intros. induction* H. Qed.

Lemma tclosure_from_rtclosure_r : forall R x y z,
  R x y -> 
  rtclosure R y z -> 
  tclosure R x z.
Proof using. intros. gen x. induction* H0. Qed.

Lemma tclosure_from_rtclosure_tclosure : forall R y x z,
  rtclosure R x y -> 
  tclosure R y z -> 
  tclosure R x z.
Proof using. intros. gen z. induction* H. Qed.

Lemma tclosure_from_tclosure_rtclosure : forall R y x z,
  tclosure R x y -> 
  rtclosure R y z -> 
  tclosure R x z.
Proof using. intros. induction* H. Qed.

End MixedClosures.

(* LATER: similar lemmas relating [rstclosure] and [stclosure] *)


(* ---------------------------------------------------------------------- *)
(** ** Irreflexive restriction of a relation *)

Definition strict A (R:binary A) : binary A :=
  fun x y => R x y /\ x <> y.

Section Strict.
Variable (A : Type).
Implicit Types R : binary A.

Lemma inverse_strict : forall R,
  inverse (strict R) = strict (inverse R).
Proof using. intros. unfold inverse, strict. extens*. Qed.

Lemma strict_l : forall y x z R,
  trans R -> 
  R x y -> 
  strict R y z -> 
  strict R x z.
Proof using. introv T H (E&H'); subst*. Qed.

Lemma strict_r : forall y x z R,
  trans R -> 
  strict R x y -> 
  R y z -> 
  strict R x z.
Proof using. introv T (E&H) H'; subst*. Qed.

Lemma trans_strict_l : forall y x z R,
  trans R -> 
  strict R x y -> 
  R y z -> 
  R x z.
Proof using. introv T (E&H) H'; subst*. Qed.

Lemma trans_strict_r : forall y x z R,
  trans R -> 
  R x y -> 
  strict R y z -> 
  R x z.
Proof using. introv T H (E&H'); subst*. Qed.

Lemma irrefl_strict : forall R,
  irrefl (strict R).
Proof using. unfold strict. intros_all~. Qed.

Lemma antisym_strict : forall R,
  antisym R -> 
  antisym (strict R).
Proof using. introv T. introv H1 H2... (* todo: bug introv *)
  unfolds strict. destruct H1; destruct H2; auto. Qed.

Lemma trans_strict : forall R,
  trans R -> 
  antisym R -> 
  trans (strict R).
Proof using.
  introv T S. unfold strict. introv [H1 H2] [H3 H4]. split.
  { apply* T. }
  { intros K. subst. apply H2. apply~ S. }
Qed.

Lemma strict_rclosure : forall R,
  irrefl R -> 
  strict (rclosure R) = R.
Proof using.
  unfold rclosure, strict. extens. intros x y. iff K.
  { autos*. }
  { split. { left*. } { apply* irrefl_neq. } }
Qed.

Lemma rclosure_strict : forall R,
  refl R -> 
  rclosure (strict R) = R.
Proof using.
  unfold rclosure, strict. extens. intros x y. iff K.
  { destruct K; subst*. }
  { tests: (x = y); subst*. }
Qed.

End Strict.


(* ********************************************************************** *)
(** Function to relation *)

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


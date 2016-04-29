(**************************************************************************
* TLC: A library for Coq                                                  *
* Binary relations                                                        *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibBool LibLogic LibProd LibSum.
Require Export LibOperation.


(* ********************************************************************** *)
(** * Generalities on binary relations *)

Definition binary (A : Type) := A -> A -> Prop.

(* ---------------------------------------------------------------------- *)
(** ** Inhabited *)

Instance binary_inhab : forall A, Inhab (binary A).
Proof using. intros. apply (prove_Inhab (fun _ _ => True)). Qed.

(* ---------------------------------------------------------------------- *)
(** ** Extensionality *)

Lemma binary_extensional : forall A (R1 R2:binary A),
  (forall x y, R1 x y <-> R2 x y) -> R1 = R2.
Proof using. intros_all. apply~ prop_ext_2. Qed.

Instance binary_extensional_inst : forall A, Extensional (binary A).
Proof using. intros. apply (Build_Extensional _ (@binary_extensional A)). Defined.


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Section Properties.
Variables (A:Type).
Implicit Types x y z : A.
Implicit Types R : binary A.

(** Reflexivity, irreflexivity, transitivity, symmetry, totality, definedness, functionality *)

Definition refl R :=
  forall x, R x x.
Definition irrefl R :=
  forall x, ~ (R x x).
Definition trans R :=
  forall y x z, R x y -> R y z -> R x z.
Definition sym R :=
  forall x y, R x y -> R y x.
Definition asym R :=
  forall x y, R x y -> ~ R y x.
Definition total R :=
  forall x y, R x y \/ R y x.
Definition defined R :=
  forall x, exists y, R x y.
  (* I would have liked to call this [total R], but this already
     means something else... *)
Definition functional R :=
  forall x y z, R x y -> R x z -> y = z.

(** Antisymmetry with respect to an equivalence relation,
    antisymmetry with respect to Leibnitz equality,
     i.e. [forall x y, R x y -> R y x -> x = y] *)

Definition antisym_wrt (E:binary A) R :=
  forall x y, R x y -> R y x -> E x y.
Definition antisym :=
  antisym_wrt (@eq A).

(** Inclusion between relations *)

Definition incl R1 R2 :=
  forall x y, R1 x y -> R2 x y.

Definition rel_le A B (P Q : A->B->Prop) :=
  forall a, pred_le (P a) (Q a).
(* TODO [incl] should be just [rel_le] *)

Lemma rel_le_refl : forall A B (P:A->B->Prop),
  rel_le P P.
Proof. intros_all~. Qed.

(** Equality between relations *)

(* TODO move further down in the file *)
(* TODO already called binary_extensional above? *)
Lemma rel_eq_intro : forall R1 R2,
  (forall x y, R1 x y <-> R2 x y) -> R1 = R2.
Proof using. intros. extens*. Qed.

Lemma rel_eq_elim : forall R1 R2,
  R1 = R2 -> (forall x y, R1 x y <-> R2 x y).
Proof using. intros. subst*. Qed.

End Properties.


(** Inclusion between a function and a relation. *)
(* TODO: maybe use longer name? *)

Definition incl_fr A B (f : A -> B) (R : A -> B -> Prop) :=
  forall x, R x (f x).
Definition incl_rf A B (R : A -> B -> Prop) (f : A -> B) :=
  forall x y, R x y -> y = f x.

(* Turning a function into a relation. *)

Definition rel_func A B (f : A -> B) :=
  fun (x : A) (y : B) => y = f x.

Lemma rel_func_equiv : forall A B (f : A -> B) (R : A -> B -> Prop),
  rel_le (rel_func f) R <-> incl_fr f R.
Proof.
  intros f R.
  unfold rel_func, incl_fr. iff H; intros x; specializes H x.
    applys* H.
    intros y Hy. subst~.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Constructions *)

Section Constructions.
Variable (A : Type).
Implicit Types R : binary A.
Implicit Types x y z : A.

(** The empty relation *)

Definition empty : binary A :=
  fun x y => False.

(** Swap (i.e. symmetric, converse, or transpose) of a relation *)

Definition flip R : binary A :=
  fun x y => R y x.

(** Complement of a relation *)

Definition compl R : binary A :=
  fun x y => ~ R y x.

(** Union of two relations *)

Definition union R1 R2 : binary A :=
  fun x y => R1 x y \/ R2 x y.

(** Strict order associated with an order, wrt Leibnitz' equality *)

Definition strict R : binary A :=
  fun x y => R x y /\ x <> y.

(** Large order associated with an order, wrt Leibnitz' equality *)

Definition large R : binary A :=
  fun x y => R x y \/ x = y.

End Constructions.

(** Inverse image *)

Definition inverse_image (A B:Type) (R:binary B) (f:A->B) : binary A :=
  fun x y => R (f x) (f y).

(** Composition of two relations, usually written [R1; R2]. *)

Definition sequence (A B C:Type) (R1:A->B->Prop) (R2:B->C->Prop) : A->C->Prop :=
  fun x z => exists y, R1 x y /\ R2 y z.

(** Pointwise product *)

Definition prod2 (A1 A2:Type)
 (R1:binary A1) (R2:binary A2) : binary (A1*A2) :=
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

(** Lexicographical order *)

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


(* ---------------------------------------------------------------------- *)
(** ** Properties of constructions *)

Section ConstructionsProp.
Variable (A : Type).
Implicit Types R : binary A.
Implicit Types x y z : A.

Lemma refl_elim : forall x y R,
  refl R -> x = y -> R x y.
Proof using. intros_all. subst~. Qed.

Lemma sym_elim : forall x y R,
  sym R -> R x y -> R y x.
Proof using. introv Sy R1. apply* Sy. Qed.

Lemma antisym_elim : forall x y R,
  antisym R -> R x y -> R y x -> x <> y -> False.
Proof using. intros_all*. Qed.

Lemma irrefl_neq : forall R,
  irrefl R ->
  forall x y, R x y -> x <> y.
Proof using. introv H P E. subst. apply* H. Qed.

Lemma irrefl_elim : forall R,
  irrefl R ->
  forall x, R x x -> False.
Proof using. introv H P. apply* H. Qed.

Lemma sym_to_eq : forall R,
  sym R ->
  forall x y, R x y = R y x.
Proof using. introv H. intros. apply prop_ext. split; apply H. Qed.

Lemma sym_flip : forall R,
  sym R -> flip R = R.
Proof using. intros. unfold flip. apply* prop_ext_2. Qed.

Lemma trans_strict : forall R,
  trans R -> antisym R -> trans (strict R).
Proof using.
  introv T S. unfold strict. introv [H1 H2] [H3 H4]. split.
    apply* T.
    intros K. subst. apply H2. apply~ S.
Qed.

Lemma flip_flip : forall R,
  flip (flip R) = R.
Proof using. intros. apply* prop_ext_2. Qed.

Lemma flip_refl : forall R,
  refl R -> refl (flip R).
Proof using. intros_all. unfolds flip. auto. Qed.

Lemma flip_trans : forall R,
  trans R -> trans (flip R).
Proof using. intros_all. unfolds flip. eauto. Qed.

Lemma flip_antisym : forall R,
  antisym R -> antisym (flip R).
Proof using. intros_all. unfolds flip. auto. Qed.

Lemma flip_asym : forall R,
  asym R -> asym (flip R).
Proof using. intros_all. unfolds flip. apply* H. Qed.

Lemma flip_total : forall R,
  total R -> total (flip R).
Proof using. intros_all. unfolds flip. auto. Qed.

Lemma flip_strict : forall R,
  flip (strict R) = strict (flip R).
Proof using. intros. unfold flip, strict. apply* prop_ext_2. Qed.

Lemma flip_large : forall R,
  flip (large R) = large (flip R).
Proof using. intros. unfold flip, large. apply* prop_ext_2. Qed.

Lemma large_refl : forall R,
  refl (large R).
Proof using. unfold large. intros_all~. Qed.

Lemma large_trans : forall R,
  trans R -> trans (large R).
Proof using. unfold large. introv Tr [H1|E1] [H2|E2]; subst*. Qed.

Lemma large_antisym : forall R,
  antisym R -> antisym (large R).
Proof using. introv T. introv H1 H2. (* todo: bug introv *)
  unfolds large. destruct H1; destruct H2; auto. Qed.

Lemma large_total : forall R,
  total R -> total (large R).
Proof using. unfold large. intros_all~. destruct* (H x y). Qed.

Lemma strict_large : forall R,
  irrefl R -> strict (large R) = R.
Proof using.
  intros. unfold large, strict. apply prop_ext_2.
  intros_all. split; intros K.
  autos*.
  split. left*. apply* irrefl_neq.
Qed.

Lemma large_strict : forall R,
  refl R -> large (strict R) = R.
Proof using.
  intros. unfold large, strict. apply prop_ext_2.
  intros_all. split; intros K.
  destruct K. autos*. subst*.
  destruct (classic (x1 = x2)). subst. right*. left*.
  (* todo: cases *)
Qed.

Lemma double_incl : forall R1 R2,
  incl R1 R2 -> incl R2 R1 -> R1 = R2.
Proof using. unfolds incl. intros. apply* prop_ext_2. Qed.

Lemma rel_incl_trans : forall R1 R2 R3,
  incl R1 R2 -> incl R2 R3 -> incl R1 R3.
Proof using.
  unfold incl. eauto.
Qed.

Lemma flip_injective : injective (@flip A).
Proof using.
  intros R1 R2 E. apply prop_ext_2. intros x y.
  unfolds flip. rewrite* (func_same_2 y x E).
Qed.

Lemma eq_by_flip_l : forall R1 R2,
  R1 = flip R2 -> flip R1 = R2.
Proof using. intros. apply flip_injective. rewrite~ flip_flip. Qed.

Lemma eq_by_flip_r : forall R1 R2,
  flip R1 = R2 -> R1 = flip R2.
Proof using. intros. apply flip_injective. rewrite~ flip_flip. Qed.

(* TODO: do we really need this extensional version? *)

Lemma flip_flip_applied : forall R x y,
  (flip (flip R)) x y = R x y.
Proof using. auto. Qed.

End ConstructionsProp.

Lemma trans_elim : forall A (y x z : A) R,
  trans R -> R x y -> R y z -> R x z.
Proof using. introv Tr R1 R2. apply* Tr. Qed.

Lemma trans_sym : forall A (y x z : A) R,
  trans R -> sym R -> R z y -> R y x -> R x z.
Proof using. introv Tr Sy R1 R2. apply* Tr. Qed.

Lemma trans_sym_1 : forall A (y x z : A) R,
  trans R -> sym R -> R y x -> R y z -> R x z.
Proof using. introv Tr Sy R1 R2. apply* Tr. Qed.

Lemma trans_sym_2 : forall A (y x z : A) R,
  trans R -> sym R -> R x y -> R z y -> R x z.
Proof using. introv Tr Sy R1 R2. apply* Tr. Qed.

Implicit Arguments trans_elim [A x z R].
Implicit Arguments trans_sym [A x z R].
Implicit Arguments trans_sym_1 [A x z R].
Implicit Arguments trans_sym_2 [A x z R].

(** Other forms of transitivity *)

Lemma large_strict_trans : forall A y x z (R:binary A),
  trans R -> large R x y -> R y z -> R x z.
Proof using. introv T [E|H] H'; subst*. Qed.

Lemma strict_large_trans : forall A y x z (R:binary A),
  trans R -> R x y -> large R y z -> R x z.
Proof using. introv T H [E|H']; subst*. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Properties about [functional] *)

(* A relation [R] is functional if and only if [flip R] composed
   with [R] is a subset of the diagonal relation [eq]. *)

Lemma functional_characterization : forall A (R : binary A),
  functional R <->
  incl (sequence (flip R) R) eq.
Proof using.
  unfold functional, incl, sequence, flip.
  split.
    introv ? [ ? [ ? ? ]]. eauto.
    eauto.
Qed.

(* The empty relation is functional. *)

Lemma functional_empty : forall A,
  functional (@empty A).
Proof using.
  unfold empty. repeat intro. tauto.
Qed.

(* The union of two functional relations is functional, provided the relations
   have disjoint domains. *)

Lemma functional_union:
  forall A (F1 F2 : binary A),
  functional F1 ->
  functional F2 ->
  (forall x y z, F1 x y -> F2 x z -> False) ->
  functional (union F1 F2).
Proof using.
  intros. unfold union. intros x y z Hxy Hxz.
  destruct Hxy, Hxz; eauto; false; eauto.
Qed.

(* TODO: a tactic "functional_exploit R" that looks for two distinct
   assumptions in the goal of the form [R ?x ?y] and produces [functional R]
   as subgoal. *)


(* ---------------------------------------------------------------------- *)
(** ** Properties about [union] *)

(* TODO: rename lemmas *)

Lemma prove_rel_union_left : forall A (R1 R2 : binary A) x y,
  R1 x y ->
  union R1 R2 x y.
Proof using.
  unfold union. eauto.
Qed.

Lemma prove_rel_union_right : forall A (R1 R2 : binary A) x y,
  R2 x y ->
  union R1 R2 x y.
Proof using.
  unfold union. eauto.
Qed.

Lemma union_covariant : forall A (R1 R2 S1 S2 : binary A),
  incl R1 S1 ->
  incl R2 S2 ->
  incl (union R1 R2) (union S1 S2).
Proof using.
  unfold incl, union. intuition eauto.
Qed.

Lemma union_refl_left : forall A (R S : binary A),
  refl R ->
  refl (union R S).
Proof using.
  unfold refl, union. eauto.
Qed.

Lemma union_symmetric:
  forall A (F1 F2 : binary A),
  union F1 F2 = union F2 F1.
Proof.
  unfold union. intros. extens; intros a b. tauto.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Properties of inclusion *)

(* TODO change hypothesis names in proofs *)
(* TODO decide whether to use a tactic exploit functional *)

(* TODO there is something by the same name in [LibBag]. *)
Lemma incl_refl : forall A (R:binary A), incl R R.
Proof using. unfolds incl. auto. Qed.

Hint Resolve incl_refl.

Lemma lexico2_incl : forall A1 A2
 (R1 R1':binary A1) (R2 R2':binary A2),
  incl R1 R1' -> incl R2 R2' -> incl (lexico2 R1 R2) (lexico2 R1' R2').
Proof using.
  introv I1 I2. intros [x1 x2] [y1 y2] [H1|[H1 H2]].
  left~. subst. right~.
Qed.

(* If [R] is defined, [S] is functional, and [R] is a subset of [S],
   then [R] equals [S]. In that case, [R] and [S] represent the graph
   of a total function. *)

Lemma defined_incl_functional:
  forall (A : Type) (R S : binary A),
  defined R ->
  functional S ->
  incl R S ->
  R = S.
Proof using.
  introv hdef hfun hincl. eapply binary_extensional. intros v w. split; intros H; eauto.
  forwards [ w' M1 ]: hdef v.
  forwards M2: hincl. eauto.
  forwards: hfun H M2. subst*.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Inclusion between a function and a relation. *)

(* If the relation [R] is functional and if [f] is included in [R],
   then [R] is included in [f], i.e., they coincide. *)

(* TODO: currently limited to the case where B = A, but it shouldn't be *)

Lemma incl_fr_functional:
  forall A (f : A -> A) (R : A -> A -> Prop),
  incl_fr f R ->
  functional R ->
  incl_rf R f.
Proof using.
  introv h1 h2. intros a b H. forwards M: h1 a. forwards*: h2 H M.
Qed.

(* Note: [incl_fr f R] implies [defined R]
         [incl_rf R f] implies [functional R] *)


(* ---------------------------------------------------------------------- *)
(** ** Properties of lexicographical composition *)

Section LexicoApp.
Variables (A1 A2 A3 A4:Type).
Variables (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4).

Lemma lexico2_app_1 : forall x1 x2 y1 y2,
  R1 x1 y1 ->
  lexico2 R1 R2 (x1,x2) (y1,y2).
Proof using. intros. left~. Qed.

Lemma lexico2_app_2 : forall x1 x2 y1 y2,
  x1 = y1 -> R2 x2 y2 ->
  lexico2 R1 R2 (x1,x2) (y1,y2).
Proof using. intros. right~. Qed.

Lemma lexico3_app_1 : forall x1 x2 x3 y1 y2 y3,
  R1 x1 y1 ->
  lexico3 R1 R2 R3 (x1,x2,x3) (y1,y2,y3).
Proof using. intros. left. left~. Qed.

Lemma lexico3_app_2 : forall x1 x2 x3 y1 y2 y3,
  x1 = y1 -> R2 x2 y2 ->
  lexico3 R1 R2 R3 (x1,x2,x3) (y1,y2,y3).
Proof using. intro. left. right~. Qed.

Lemma lexico3_app_3 : forall x1 x2 x3 y1 y2 y3,
  x1 = y1 -> x2 = y2 -> R3 x3 y3 ->
  lexico3 R1 R2 R3 (x1,x2,x3) (y1,y2,y3).
Proof using. intros. right~. Qed.

Lemma lexico4_app_1 : forall x1 x2 x3 x4 y1 y2 y3 y4,
  R1 x1 y1 ->
  lexico4 R1 R2 R3 R4 (x1,x2,x3,x4) (y1,y2,y3,y4).
Proof using. intros. left. left. left~. Qed.

Lemma lexico4_app_2 : forall x1 x2 x3 x4 y1 y2 y3 y4,
  x1 = y1 -> R2 x2 y2 ->
  lexico4 R1 R2 R3 R4 (x1,x2,x3,x4) (y1,y2,y3,y4).
Proof using. intros. left. left. right~. Qed.

Lemma lexico4_app_3 : forall x1 x2 x3 x4 y1 y2 y3 y4,
  x1 = y1 -> x2 = y2 -> R3 x3 y3 ->
  lexico4 R1 R2 R3 R4 (x1,x2,x3,x4) (y1,y2,y3,y4).
Proof using. intros. left. right~. Qed.

Lemma lexico4_app_4 : forall x1 x2 x3 x4 y1 y2 y3 y4,
  x1 = y1 -> x2 = y2 -> x3 = y3 -> R4 x4 y4 ->
  lexico4 R1 R2 R3 R4 (x1,x2,x3,x4) (y1,y2,y3,y4).
Proof using. intros. right~. Qed.

End LexicoApp.

(** Transitivity *)

Lemma lexico2_trans : forall A1 A2
 (R1:binary A1) (R2:binary A2),
  trans R1 -> trans R2 -> trans (lexico2 R1 R2).
Proof using.
  introv Tr1 Tr2. intros [x1 x2] [y1 y2] [z1 z2] Rxy Ryz.
  simpls. destruct Rxy as [L1|[Eq1 L1]];
   destruct Ryz as [M2|[Eq2 M2]]; subst*.
Qed.

Lemma lexico3_trans : forall A1 A2 A3
 (R1:binary A1) (R2:binary A2) (R3:binary A3),
  trans R1 -> trans R2 -> trans R3 -> trans (lexico3 R1 R2 R3).
Proof using.
  introv Tr1 Tr2 Tr3. applys~ lexico2_trans. applys~ lexico2_trans.
Qed.

Lemma lexico4_trans : forall A1 A2 A3 A4
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4),
  trans R1 -> trans R2 -> trans R3 -> trans R4 -> trans (lexico4 R1 R2 R3 R4).
Proof using.
  introv Tr1 Tr2 Tr3. applys~ lexico3_trans. applys~ lexico2_trans.
Qed.



(* ********************************************************************** *)
(** * Equivalence relations *)

Record equiv A (R:binary A) :=
 { equiv_refl : refl R;
   equiv_sym : sym R;
   equiv_trans : trans R }.

(** Equality is an equivalence *)

Lemma eq_equiv : forall A, equiv (@eq A).
Proof using. intros. constructor; intros_all; subst~. Qed.

Hint Resolve eq_equiv.

(** Symmetric of an equivalence is an equivalence *)

Lemma flip_equiv : forall A (E:binary A),
  equiv E -> equiv (flip E).
Proof using.
  introv Equi. unfold flip. constructor; intros_all;
    dintuition eauto.
Qed.

(** Product of two equivalences is an equivalence *)

Lemma prod2_equiv : forall A1 A2 (E1:binary A1) (E2:binary A2),
  equiv E1 -> equiv E2 -> equiv (prod2 E1 E2).
Proof using.
  introv Equi1 Equi2. constructor.
  intros [x1 x2]. simpl. dintuition.
  intros [x1 x2] [y1 y2]. simpl. dintuition.
  intros [x1 x2] [y1 y2] [z1 z2]. simpl. dintuition eauto.
Qed.
(* NEWCOQ: clean above *)

(* todo: other arities of Prod *)


(**************************************************************************)
(* * Closures *)

(* TODO: eliminate the use of the section variable R *)

Section Closures.
Variables (A : Type) (R : binary A).

(* ---------------------------------------------------------------------- *)
(** ** Constructions *)

(** Reflexive-transitive closure ( R* ) *)

Inductive rtclosure : binary A :=
  | rtclosure_refl : forall x,
      rtclosure x x
  | rtclosure_step : forall y x z,
      R x y -> rtclosure y z -> rtclosure x z.

(** Transitive closure ( R+ ) *)

Inductive tclosure : binary A :=
  | tclosure_intro : forall x y z,
     R x y -> rtclosure y z -> tclosure x z.

(** Another definition of transitive closure ( R+ ) *)

Inductive tclosure' : binary A :=
  | tclosure'_step : forall x y,
     R x y -> tclosure' x y
  | tclosure'_trans : forall y x z,
     tclosure' x y -> tclosure' y z -> tclosure' x z.

(** Symmetric-transitive closure *)

Inductive stclosure (A:Type) (R:binary A) : binary A :=
  | stclosure_step : forall x y,
      R x y -> stclosure R x y
  | stclosure_sym : forall x y,
      stclosure R x y -> stclosure R y x
  | stclosure_trans : forall y x z,
      stclosure R x y -> stclosure R y z -> stclosure R x z.



(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Hint Constructors tclosure rtclosure equiv.

Lemma rtclosure_once : forall x y,
  R x y -> rtclosure x y.
Proof using. autos*. Qed.

Hint Resolve rtclosure_once.

Lemma rtclosure_trans : trans rtclosure.
Proof using. introv R1 R2. induction* R1. Qed.

Lemma rtclosure_last : forall y x z,
  rtclosure x y -> R y z -> rtclosure x z.
Proof using. introv R1 R2. induction* R1. Qed.

Hint Resolve rtclosure_trans.

Lemma tclosure_once : forall x y,
  R x y -> tclosure x y.
Proof using. eauto. Qed.

Lemma tclosure_rtclosure : forall x y,
  tclosure x y -> rtclosure x y.
Proof using. intros. destruct* H. Qed.

Hint Resolve tclosure_once tclosure_rtclosure.

Lemma tclosure_rtclosure_step : forall x y z,
  rtclosure x y -> R y z -> tclosure x z.
Proof using. intros. induction* H. Qed.

Lemma tclosure_tclosure_step : forall x y z,
  tclosure x y -> R y z -> tclosure x z.
Proof. introv C H. applys tclosure_rtclosure_step H. apply* tclosure_rtclosure. Qed.

Lemma tclosure_step_rtclosure : forall x y z,
  R x y -> rtclosure y z -> tclosure x z.
Proof using. intros. gen x. induction* H0. Qed.

Lemma tclosure_step_tclosure : forall x y z,
  R x y -> tclosure y z -> tclosure x z.
Proof using. intros. inverts* H0. Qed.

Hint Resolve tclosure_rtclosure_step tclosure_step_rtclosure.

Lemma tclosure_rtclosure_tclosure : forall y x z,
  rtclosure x y -> tclosure y z -> tclosure x z.
Proof using. intros. gen z. induction* H. Qed.

Lemma tclosure_tclosure_rtclosure : forall y x z,
  tclosure x y -> rtclosure y z -> tclosure x z.
Proof using. intros. induction* H. Qed.

Lemma tclosure_trans : trans tclosure.
Proof using. intros_all. autos* tclosure_tclosure_rtclosure. Qed.

Lemma tclosure_tclosure' : forall x y,
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

Lemma rtclosure_ind_right : forall (P : A -> A -> Prop),
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

Lemma tclosure_ind_right : forall A (R : binary A) (P : A -> A -> Prop),
  (forall x y, R x y -> P x y) ->
  (forall y x z, tclosure R x y -> P x y -> R y z -> P x z) ->
  forall x y, tclosure R x y -> P x y.
Proof.
  introv S Ind H. inverts H as HR HC.
  induction HC using rtclosure_ind_right.
   apply* S.
   applys Ind; try apply* tclosure_step_rtclosure; autos*.
Qed.

Hint Resolve rtclosure_refl rtclosure_step rtclosure_once : rtclosure.
(* TODO: should rename and complete the [closure] database *)
(* TODO: should not need to re-export the following version *)

Lemma tclosure_right : forall A (R : binary A) x y,
  tclosure R x y ->
  exists z, rtclosure R x z /\ R z y.
Proof.
  introv H. induction H using tclosure_ind_right.
   exists x. splits~. constructors~.
   exists y. splits~. apply~ tclosure_rtclosure.
Qed.

Lemma incl_tclosure_self : forall A (R:binary A),
   incl R (tclosure R).
Proof using. unfolds incl. intros. apply~ tclosure_once. Qed.
Hint Resolve incl_tclosure_self.

(* TODO: sort and complete the following *)

Hint Resolve stclosure_step stclosure_sym stclosure_trans.

Lemma stclosure_le : forall A (R1 R2 : binary A),
  incl R1 R2 -> incl (stclosure R1) (stclosure R2).
Proof using. unfolds incl. introv Le H. induction* H. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Additional definitions *)

(* TODO: move above once section has been eliminated *)
(* A theory of [rstclosure]. *)

Inductive rstclosure (A : Type) (R : binary A) : binary A :=
  | rstclosure_step : forall x y,
      R x y -> rstclosure R x y
  | rstclosure_refl : forall x,
      rstclosure R x x
  | rstclosure_sym : forall x y,
      rstclosure R x y -> rstclosure R y x
  | rstclosure_trans : forall y x z,
      rstclosure R x y -> rstclosure R y z -> rstclosure R x z.

(** Symmetric closure *)

Definition sclosure (A:Type) (R:binary A) : binary A :=
  fun x y => R x y \/ R y x.

(* ---------------------------------------------------------------------- *)
(** ** Hints *)

Hint Constructors tclosure : tclosure.
Hint Constructors rstclosure : rstclosure.
Hint Constructors stclosure : stclosure.
Hint Unfold sclosure : sclosure.


(* ---------------------------------------------------------------------- *)
(** ** Additional properties *)

(* TODO: check name of lemmas below, and sort lemmas *)

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
  incl R S ->
  incl (rstclosure R) (rstclosure S).
Proof using.
  unfold incl. induction 2; eauto with rstclosure.
Qed.

Lemma rstclosure_inflationary: forall A (R : binary A),
  incl R (rstclosure R).
Proof using.
  unfold incl. eauto with rstclosure.
Qed.

Lemma prove_rstclosure_incl : forall A (R S : binary A),
  incl R (rstclosure S) ->
  incl (rstclosure R) (rstclosure S).
Proof using.
  unfold incl. induction 2; eauto with rstclosure.
Qed.

Lemma rtclosure_union : forall A (R S : binary A),
  incl (union (rtclosure R) (rtclosure S))
       (rtclosure (union R S)).
Proof using.
  unfold incl, union. intros ? ? ? x y H.
  destruct H; gen x y;
  induction 1; eauto with rtclosure.
Qed.

Lemma rstclosure_union : forall A (R S : binary A),
  incl (union (rstclosure R) (rstclosure S))
       (rstclosure (union R S)).
Proof using.
  unfold incl, union. intros ? ? ? x y H.
  destruct H; gen x y;
  induction 1; eauto with rstclosure.
Qed.


Lemma sym_sclosure : forall A (R : binary A),
  sym (sclosure R).
Proof using.
  unfold sym, sclosure. tauto.
Qed.

Lemma sclosure_is_a_closure_operator : forall A (R1 R2 : binary A),
  incl R1 (sclosure R2) ->
  incl (sclosure R1) (sclosure R2).
Proof using.
  unfold sclosure, incl. introv h. introv H.
  destruct H.
  { eauto. }
  { forwards M: h. eauto. destruct M; tauto. }
Qed.

Lemma sclosure_covariant : forall A (R1 R2 : binary A),
  incl R1 R2 ->
  incl (sclosure R1) (sclosure R2).
Proof using.
  unfold sclosure, incl. introv M H. destruct H; eauto.
Qed.

Lemma rtclosure_covariant : forall A (R1 R2 : binary A),
  incl R1 R2 ->
  incl (rtclosure R1) (rtclosure R2).
Proof using.
  unfold incl. induction 2; eauto with rtclosure.
Qed.

Lemma tclosure_covariant : forall A (R1 R2 : binary A),
  incl R1 R2 ->
  incl (tclosure R1) (tclosure R2).
Proof using.
  unfold incl. inversion 2; subst. econstructor.
  eauto.
  eapply rtclosure_covariant; eauto.
Qed.

Lemma tclosure_last : forall A (R : binary A) y x z,
  tclosure R x y -> R y z -> tclosure R x z.
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

Lemma sclosure_incl_stclosure : forall A (R : binary A),
  incl (sclosure R) (stclosure R).
Proof using.
  unfold incl. inversion 1; eauto with stclosure.
Qed.

Lemma tclosure_incl_stclosure : forall A (R1 R2 : binary A),
  incl R1 (stclosure R2) ->
  incl (tclosure R1) (stclosure R2).
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
    eapply tclosure_incl_stclosure; [ | eassumption ].
    eapply sclosure_incl_stclosure. }
Qed.


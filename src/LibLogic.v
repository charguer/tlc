(**************************************************************************
* TLC: A library for Coq                                                  *
* Properties of logical connectives and functions                         *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics.
From TLC Require Export LibAxioms LibEqual.
Generalizable Variables A B P.


(* ********************************************************************** *)
(** * Strong existentials *)

(** Type [sig] is defined in LibLogicCore *)

(** Projections *)

Definition sig_val (A : Type) (P : A->Prop) (e : sig P) : A :=
  match e with exist _ a _ => a end.

Definition sig_proof (A : Type) (P : A->Prop) (e : sig P) : P (sig_val e) :=
  match e with exist _ _ b => b end.


(* ********************************************************************** *)
(** * Inhabited types *)

(* ---------------------------------------------------------------------- *)
(** ** Typeclass for describing inhabited types *)

(** The proposition [Inhab A] captures the fact that the type [A] is
    inhabited (i.e., there exists at least one value of type [A]). *)

Class Inhab (A:Type) : Prop :=
  { Inhab_intro : (exists (x:A), True) }.

#[global]
Hint Mode Inhab + : typeclass_instances.


(* ---------------------------------------------------------------------- *)
(** ** Tactics taking into account *)

(** Extension to LibTactics' fast introduction tactic [=>>]
    to handle specifically the case of the Inhabited typeclass. *)

Ltac intro_nondeps_aux_special_intro G ::=
  match G with
  | (Inhab _) => idtac
  end.


(* ---------------------------------------------------------------------- *)
(** ** Arbitrary values for inhabited types *)

(** The value [arbitrary] can be used as a dummy value at any place
    where a value of an inhabited type is expected. *)

Definition arbitrary `{Inhab A} : A :=
  sig_val (@indefinite_description A _ Inhab_intro).

(** Extraction of [arbitrary] constants as a runtime error. *)

(* Extract Constant arbitrary => "(raise Not_found)". *)


(* ---------------------------------------------------------------------- *)
(** ** Lemmas about inhabited types *)

(** Proving a type to be inhabited *)

Lemma Inhab_of_val : forall (A:Type),
  A ->
  Inhab A.
Proof using. intros A x. constructor. exists x. auto. Qed.

(** Arrows are inhabited if their codomain is inhabited. *)

#[global]
Instance Inhab_impl : forall A B {I:Inhab B},
  Inhab (A -> B).
Proof using. intros. apply (Inhab_of_val (fun _ => arbitrary)). Qed.



(* ********************************************************************** *)
(** * Non-constructive conditionals *)

(* ---------------------------------------------------------------------- *)
(** ** Excluded middle *)

(** Every proposition is either [True] or [False]. *)

Lemma classic : forall (P : Prop),
  P \/ ~ P.
Proof using.
  intros.
  set (B1 := fun b => b = true \/ P).
  set (B2 := fun b => b = false \/ P).
  asserts H1: (ex B1). exists true. left~.
  asserts H2: (ex B2). exists false. left~.
  sets i1: (indefinite_description H1).
  sets i2: (indefinite_description H2).
  destruct (sig_proof i1) as [HA|]; [|auto].
  destruct (sig_proof i2) as [HB|]; [|auto].
  right. intros HP. asserts EB: (B1 = B2).
    apply pred_ext_1. intros b. split; intros _; right; auto.
  subst i1 i2. destruct EB.
  rewrite (proof_irrelevance H2 H1) in HB. congruence.
Qed.

Definition prop_inv := classic.


(* ---------------------------------------------------------------------- *)
(** ** Strong excluded middle *)

(** From classical logic and indefinite description, we can prove
    the strong (or informative) excluded middle, which allows Coq
    definitions to make a case analysis on the truth value of any
    proposition. *)

Lemma classicT : forall (P : Prop),
  {P} + {~ P}.
Proof using.
  intros. pose (select := fun (b:bool) => if b then P else ~P).
  cuts (M,HP): { b:bool | select b }.
    destruct M. left~. right~.
  apply indefinite_description.
  destruct (prop_inv P). exists~ true. exists~ false.
Qed.

(** Simplification lemmas *)

Lemma classicT_l : forall (P : Prop) (H:P),
   classicT P = left _ H.
Proof using. intros. destruct (classicT P). fequals. false~. Qed.

Lemma classicT_r : forall (P : Prop) (H:~P),
   classicT P = right _ H.
Proof using. intros. destruct (classicT P). false~. fequals. Qed.


(* ---------------------------------------------------------------------- *)
(** ** If-then-else on propositions *)

(** The expression [If P then v1 else v2] can be used to build
    a conditional that depends on a proposition [P]. *)

Notation "'If' P 'then' v1 'else' v2" :=
  (if (classicT P) then v1 else v2)
  (at level 200, right associativity) : type_scope.

Section Ifthenelse.
Variables A : Type.
Implicit Types P : Prop.
Implicit Types x y : A.

(** Lemmas to simplify If-then-else statement *)

Lemma If_l : forall P x y,
  P ->
  (If P then x else y) = x.
Proof using. intros. case_if*. Qed.

Lemma If_r : forall P x y,
  ~ P ->
  (If P then x else y) = y.
Proof using. intros. case_if*. Qed.

(** A lemma to prove an equality between two If-then-else *)

Lemma If_eq : forall P P' x x' y y',
  (P <-> P') ->
  (P -> x = x') ->
  (~P -> y = y') ->
  (If P then x else y) = (If P' then x' else y').
Proof using. intros. do 2 case_if; autos*. Qed.

(** A simpler version of the above lemma *)

Lemma If_eq_simple : forall P P' x x' y y',
  (P <-> P') ->
  (x = x') ->
  (y = y') ->
  (If P then x else y) = (If P' then x' else y').
Proof using. intros. subst. asserts_rewrite (P = P'). apply~ prop_ext. auto. Qed.

End Ifthenelse.


(* ---------------------------------------------------------------------- *)
(** ** Consequences *)

(** Propositional extensionality stated using itself *)

Lemma eq_prop_eq_iff : forall P Q,
  (P = Q) = (P <-> Q).
Proof using. intros. extens. iff. subst*. apply~ prop_ext. Qed.

(** Propositional completeness (degeneracy) *)

Lemma prop_degeneracy : forall (P : Prop),
   P = True \/ P = False.
Proof using.
  intros. destruct (prop_inv P).
    left. apply* prop_ext.
    right. apply* prop_ext.
Qed.

(** Independence of general premises *)

Lemma indep_general_premises :
  forall A `{Inhab A} (P : A -> Prop) (Q : Prop),
  (Q -> exists x, P x) ->
  (exists x, Q -> P x).
Proof using.
  introv I M. destruct (prop_inv Q).
  destruct* (M H).
  exists (arbitrary (A:=A)). auto_false.
Qed.

(** Small drinker's paradox *)

Lemma small_drinker_paradox : forall `{Inhab A} (P : A -> Prop),
  exists x, (exists x, P x) -> P x.
Proof using.
  intros A I P. destruct (prop_inv (exists x, P x)).
  destruct H. exists x. auto.
  exists (arbitrary (A:=A)). auto_false.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Tactic for proving tautologies by bruteforce case-analysis *)

(** The tactic [tautop P1 .. PN] helps performing case analysis on
    the propositions/booleans that are given to it as parameters. *)

Ltac tautop_case P :=
  match type of P with
  | Prop => destruct (prop_degeneracy P)
  | bool => destruct P
  end.

Ltac tautop_pre tt :=
  intros;
  repeat rewrite eq_prop_eq_iff in *.

Ltac tautop_post tt :=
  subst;
  try solve [ intuition auto_false ].

Ltac tautop_core args :=
  tautop_pre tt;
  let rec aux Ps :=
    match Ps with
    | nil => idtac
    | cons (boxer ?P) ?Ps' => tautop_case P; aux Ps'
    end in
  aux args;
  tautop_post tt.

Ltac tautop_noargs tt :=
  let rec aux Ps :=
     match goal with
     | |- forall (_:Prop), _ =>
       let P := fresh "P" in intro P; aux (cons (boxer P) Ps)
     | _ => tautop_core Ps
     end
     in
  aux constr:(@nil Boxer).

Tactic Notation "tautop" :=
  tautop_noargs tt.
Tactic Notation "tautop" constr(P1) :=
  tautop_core (>> P1).
Tactic Notation "tautop" constr(P1) constr(P2) :=
  tautop_core (>> P1 P2).
Tactic Notation "tautop" constr(P1) constr(P2) constr(P3) :=
  tautop_core (>> P1 P2 P3).


(* ********************************************************************** *)
(** * Properties of logical combinators *)

(* ---------------------------------------------------------------------- *)
(** ** Simplification of conjunction and disjunction *)

Section SimplConjDisj.
Implicit Types P Q : Prop.

Lemma and_True_l_eq : forall P,
  (True /\ P) = P.
Proof using. tautop. Qed.

Lemma and_True_r_eq : forall P,
  (P /\ True) = P.
Proof using. tautop. Qed.

Lemma and_False_l_eq : forall P,
  (False /\ P) = False.
Proof using. tautop. Qed.

Lemma and_False_r_eq : forall P,
  (P /\ False) = False.
Proof using. tautop. Qed.

Lemma or_True_l_eq : forall P,
  (True \/ P) = True.
Proof using. tautop. Qed.

Lemma or_True_r_eq : forall P,
  (P \/ True) = True.
Proof using. tautop. Qed.

Lemma or_False_l_eq : forall P,
  (False \/ P) = P.
Proof using. tautop. Qed.

Lemma or_False_r_eq : forall P,
  (P \/ False) = P.
Proof using. tautop. Qed.

End SimplConjDisj.


(* ---------------------------------------------------------------------- *)
(** ** Distribution of negation on basic operators *)

Section SimplNot.
Implicit Types P Q : Prop.

Lemma not_True_eq :
  (~ True) = False.
Proof using. tautop. Qed.

Lemma not_False_eq :
  (~ False) = True.
Proof using. tautop. Qed.

Lemma not_not_eq : forall P,
  (~ (~ P)) = P.
Proof using. tautop. Qed.

Lemma not_and_eq : forall P Q,
  (~ (P /\ Q)) = (~ P \/ ~ Q).
Proof using. tautop. Qed.

Lemma not_or_eq : forall P Q,
  (~ (P \/ Q)) = (~ P /\ ~ Q).
Proof using. tautop. Qed.

Lemma not_impl_eq : forall P Q,
  (~ (P -> Q)) = (P /\ ~ Q).
Proof using. tautop. Qed.

(* Derived versions *)

Lemma not_or_nots_eq : forall P Q,
  (~ (~ P \/ ~ Q)) = (P /\ Q).
Proof using. tautop. Qed.

Lemma not_and_nots_eq : forall P Q,
  (~ (~ P /\ ~ Q)) = (P \/ Q).
Proof using. tautop. Qed.

End SimplNot.


(* ---------------------------------------------------------------------- *)
(** ** Double negation and contrapose *)

Section DoubleNeg.
Implicit Types P Q : Prop.

(** Double negation *)

Lemma not_not_inv : forall P,
  ~ ~ P ->
  P.
Proof using. tautop. Qed.

Lemma not_not : forall P,
  P ->
  ~ ~ P.
Proof using. tautop. Qed.

(** Contrapose *)

Lemma contrapose_eq : forall P Q,
  (~ P -> ~ Q) = (Q -> P).
Proof using. tautop. Qed.

Lemma contrapose_inv : forall P Q,
  (~ Q -> ~ P) ->
  (P -> Q).
Proof using. tautop. Qed.

Lemma contrapose : forall P Q,
  (Q -> P) ->
  (~ P -> ~ Q).
Proof using. tautop. Qed.

(** Negation is injective *)

Lemma injective_not : forall P Q,
  (~P) = (~Q) ->
  (P = Q).
Proof using. tautop. Qed.

End DoubleNeg.


(* ---------------------------------------------------------------------- *)
(** ** Distribution of negation on quantifiers *)

Section SimplNotQuantifiers.
Variables (A : Type).
Implicit Types P : A -> Prop.

(** Three auxiliary facts (private lemmas) *)

Lemma exists_of_not_forall : forall P,
  ~ (forall x, ~ P x) ->
  (exists x, P x).
Proof using. intros. apply* not_not_inv. Qed.

Lemma forall_of_not_exists : forall P,
  ~ (exists x, ~ P x) ->
  (forall x, P x).
Proof using. intros. apply* not_not_inv. Qed.

Lemma not_not_pred_eq : forall A (P:A->Prop),
  P = (fun x => ~ ~ (P x)).
Proof using. intros. extens. intros. rewrite* not_not_eq. Qed.

(** Rewriting rules for quantifiers *)

Lemma not_forall_eq : forall P,
  (~ (forall x, P x)) = (exists x, ~ P x).
Proof using.
  extens. iff.
  { apply exists_of_not_forall. rewrite~ (not_not_pred_eq P) in H. }
  { intros M. destruct~ H as [x Cx]. }
Qed.

Lemma not_exists_eq : forall P,
  (~ (exists x, P x)) = (forall x, ~ P x).
Proof using.
  intros. apply injective_not. rewrite not_forall_eq.
  rewrite not_not_eq. set (P':=P) at 1.
  rewrite~ (not_not_pred_eq P').
Qed.

(* Derived versions, useful when rewriting does not work
   under binders. *)

Lemma not_forall_not_eq : forall P,
  (~ (forall x, ~ P x)) = (exists x, P x).
Proof using.
  intros. rewrite not_forall_eq.
   set (P':=P) at 2. rewrite~ (not_not_pred_eq P').
Qed.

Lemma not_exists_not_eq : forall P,
  (~ (exists x, ~ P x)) = (forall x, P x).
Proof using.
  intros. rewrite not_exists_eq.
  set (P':=P) at 2. rewrite~ (not_not_pred_eq P').
Qed.

End SimplNotQuantifiers.


(* ---------------------------------------------------------------------- *)
(** ** Propositions equal to [True] or [False] *)

Section EqTrueFalse.
Implicit Types P Q : Prop.

(** Propositions equal to [True] *)

Lemma prop_eq_True_eq : forall P,
  (P = True) = P.
Proof using. tautop. Qed.

Lemma prop_eq_True : forall P,
  P ->
  P = True.
Proof using. tautop. Qed.

Lemma prop_eq_True_inv : forall P,
  P = True ->
  P.
Proof using. tautop. Qed.

(** Propositions equal to [False] *)

Lemma prop_eq_False_eq : forall P,
  (P = False) = ~ P.
Proof using. tautop. Qed.

Lemma prop_eq_False : forall P,
  ~ P ->
  P = False.
Proof using. tautop. Qed.

Lemma prop_eq_False_inv : forall P,
  P = False ->
  ~ P.
Proof using. tautop. Qed.

End EqTrueFalse.

#[global]
Hint Resolve prop_eq_True prop_eq_False.


(* ---------------------------------------------------------------------- *)
(** ** Disequal propositions *)

Section NeqProp.
Implicit Types P Q : Prop.

(** Propositions not [True] or not [False] *)

Lemma prop_neq_True_eq : forall P,
  (P <> True) = ~ P.
Proof using. tautop. Qed.

Lemma prop_neq_False_eq : forall P,
  (P <> False) = P.
Proof using. tautop. Qed.

(** Proving two propositions not equal *)

Lemma prop_neq_of_iff_l : forall P Q,
  (P <-> ~ Q) ->
  P <> Q.
Proof using. tautop. Qed.

Lemma prop_neq_of_iff_r : forall P Q,
  (~ P <-> Q) ->
  P <> Q.
Proof using. tautop. Qed.

Lemma prop_neq_inv_iff_l : forall P Q,
  P <> Q ->
  (P <-> ~ Q).
Proof using. tautop. Qed.

Lemma prop_neq_inv_iff_r : forall P Q,
  P <> Q ->
  (~ P <-> Q).
Proof using. tautop. Qed.

(** True is not False *)

Lemma True_neq_False : True <> False.
Proof using. tautop. Qed.

End NeqProp.

#[global]
Hint Resolve True_neq_False.


(* ---------------------------------------------------------------------- *)
(** ** Peirce rule and similar *)

Section ClassicOr.
Implicit Types P Q : Prop.

(** Peirce's result: proving a fact by assuming its negation *)

Lemma assume_not : forall P,
  (~ P -> P) ->
  P.
Proof using. tautop. Qed.

(** Proving a disjunction, assuming the negation of the other branch *)

Lemma or_classic_l : forall P Q,
  (~ Q -> P) ->
  P \/ Q.
Proof using. tautop. Qed.

Lemma or_classic_r : forall P Q,
  (~ P -> Q) ->
  P \/ Q.
Proof using. tautop. Qed.

(** Same, but in forward style *)

Lemma or_inv_classic_l : forall P Q,
  P \/ Q ->
  (P \/ (~ P /\ Q)).
Proof using. tautop. Qed.

Lemma or_inv_classic_r : forall P Q,
  P \/ Q ->
  (Q \/ (P /\ ~ Q)).
Proof using. tautop. Qed.

End ClassicOr.


(* ---------------------------------------------------------------------- *)
(** ** Properties of logical equivalence *)

Section IffProp.
Implicit Types P Q R : Prop.

(** Introduction *)

Lemma iff_eq_and : forall P Q : Prop,
  (P <-> Q) = ((P -> Q) /\ (Q -> P)).
Proof using. tautop. Qed.

Lemma iff_intro : forall P Q : Prop,
  (P -> Q) ->
  (Q -> P) ->
  (P <-> Q).
Proof using. intros. rewrite* iff_eq_and. Qed.

(** Reflexivity: [refl iff] *)

Lemma iff_refl : forall P,
  P <-> P.
Proof using. tautop. Qed.

(** Symmetry: [sym iff] *)

Lemma iff_sym : forall P Q,
  (P <-> Q) ->
  (Q <-> P).
Proof using. tautop. Qed.

(** Transitivity: [trans iff] *)

Lemma iff_trans : forall P Q R,
  (P <-> Q) ->
  (Q <-> R) ->
  (P <-> R).
Proof using. tautop. Qed.

(** First projection *)

Lemma iff_l : forall P Q,
  (P <-> Q) ->
  P ->
  Q.
Proof using. tautop. Qed.

(** Second projection *)

Lemma iff_r : forall P Q,
  (P <-> Q) ->
  Q ->
  P.
Proof using. tautop. Qed.

(** Contrapose of the first projection *)

Lemma iff_not_l : forall P Q,
  (P <-> Q) ->
  ~ P ->
  ~ Q.
Proof using. tautop. Qed.

(** Contrapose of the second projection *)

Lemma iff_not_r : forall P Q,
  (P <-> Q) ->
  ~ Q ->
  ~ P.
Proof using. tautop. Qed.

(** Negation can change side of an equivalence *)

Lemma iff_not_swap_eq : forall P Q,
  ((~ P) <-> Q) = (P <-> (~ Q)).
Proof using. tautop. Qed.

(** Negation can be cancelled on both sides *)

Lemma iff_not_not_eq : forall P Q,
  ((~ P) <-> (~Q)) = (P <-> Q).
Proof using. tautop. Qed.

End IffProp.


(* ********************************************************************** *)
(** * Tactics *)

(* ---------------------------------------------------------------------- *)
(** ** Tactic for simplifying expressions *)

(** The tactic [rew_logic] can be used to automatically
    simplify logical expressions. Syntax [rew_logic in H]
    and [rew_logic in *] are also available. *)

(* Remark: [not_impl] needs to have higher priority than [not_forall],
   and samewise for [not_forall_not_eq] and [not_exists_not_eq]. *)
#[global]
Hint Rewrite
  not_not_eq not_and_eq not_or_eq not_impl_eq not_True_eq not_False_eq
  not_forall_eq not_forall_not_eq
  not_exists_eq not_exists_not_eq not_impl_eq
  prop_eq_True_eq prop_eq_False_eq eq_prop_eq_iff
  and_True_l_eq and_True_r_eq and_False_l_eq and_False_r_eq
  or_True_l_eq or_True_r_eq or_False_l_eq or_False_r_eq
  not_False_eq not_True_eq
  : rew_logic.

Tactic Notation "rew_logic" :=
  autorewrite with rew_logic.
Tactic Notation "rew_logic" "in" hyp(H) :=
  autorewrite with rew_logic in H.
Tactic Notation "rew_logic" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_logic).
  (* autorewrite with rew_logic in *. *)

Tactic Notation "rew_logic" "~" :=
  rew_logic; auto_tilde.
Tactic Notation "rew_logic" "~" "in" hyp(H) :=
  rew_logic in H; auto_tilde.
Tactic Notation "rew_logic" "~" "in" "*" :=
  rew_logic in *; auto_tilde.

Tactic Notation "rew_logic" "*" :=
  rew_logic; auto_star.
Tactic Notation "rew_logic" "*" "in" hyp(H) :=
  rew_logic in H; auto_star.
Tactic Notation "rew_logic" "*" "in" "*" :=
  rew_logic in *; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [tests: P] for classical disjunction on [P]. *)

(** The tactic [tests: P] can be used to tests whether the proposition [P]
    is true or not. If [P] is an equality, it is substituted. Use the
    tactic [tests_nosubst: P] to disable the automated substitution.
    Use the tactic [tests_basic: P] to moreover disable simplification
    of logical expressions.
    To name the resulting hypotheses use [tests I: P], or [tests I1 I2: P]
    to assign different names to both sides.
    (In LibReflect, the tactic is extended so that [P] can be a boolean.) *)

Ltac tests_ssum_base E H1 H2 :=
  destruct E as [H1|H2].

Ltac tests_prop_base E H1 H2 :=
  tests_ssum_base (classicT E) H1 H2.

Ltac tests_dispatch E H1 H2 :=
  match type of E with
  | Prop => tests_prop_base E H1 H2
  | {_}+{_} => tests_ssum_base E H1 H2
  end.

Ltac tests_post H introstac :=
  tryfalse; rew_logic in H; revert H;
  introstac tt; tryfalse.

Ltac tests_post_subst H I :=
  tests_post H ltac:(fun _ => first [ intro_subst_hyp | intros I ]).

Ltac tests_post_nosubst H I :=
  tests_post H ltac:(fun _ => intros I).

Ltac tests_base E I1 I2 tests_post :=
  let H1 := fresh "TEMP" in
  let H2 := fresh "TEMP" in
  tests_dispatch E H1 H2;
    [ tests_post H1 I1
    | tests_post H2 I2 ].

Tactic Notation "tests" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E) :=
  tests_base E I1 I2 ltac:(tests_post_subst).
Tactic Notation "tests" simple_intropattern(I) ":" constr(E) :=
  tests I I: E.
Tactic Notation "tests" ":" constr(E) :=
  let I := fresh "C" in tests I: E.
Tactic Notation "tests" "~" ":" constr(E) :=
  tests: E; auto_tilde.
Tactic Notation "tests" "*" ":" constr(E) :=
  tests: E; auto_star.

Tactic Notation "tests_nosubst" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E) :=
  tests_base E I1 I2 ltac:(tests_post_nosubst).
Tactic Notation "tests_nosubst" simple_intropattern(I) ":" constr(E) :=
  tests_nosubst I I: E.
Tactic Notation "tests_nosubst" ":" constr(E) :=
  let I := fresh "C" in tests I: E.
Tactic Notation "tests_nosubst" "~" ":" constr(E) :=
  tests: E; auto_tilde.
Tactic Notation "tests_nosubst" "*" ":" constr(E) :=
  tests: E; auto_star.

Tactic Notation "tests_basic" simple_intropattern(I1) simple_intropattern(I2) ":" constr(E) :=
  tests_dispatch E I1 I2.
Tactic Notation "tests_basic" simple_intropattern(I1) ":" constr(E) :=
  tests_basic I1 I1: E.
Tactic Notation "tests_basic" ":" constr(E) :=
  let C := fresh "C" in tests_basic C: E.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [case_classic] *)

(** [case_classic] performs a case analysis on the first expression of the
    form [classicT ?E] that appears in the goal. *)

Tactic Notation "case_classic" "as" simple_intropattern(C) :=
  match goal with
  | |- context [ classicT ?E ] => destruct (classicT E) as [C|C]
  | H: context [ classicT ?E ] |- _ => destruct (classicT E) as [C|C]
  end; tryfalse.

Tactic Notation "case_classic" :=
  let C := fresh "C" in case_classic as C.


(* ---------------------------------------------------------------------- *)
(** ** Tactic [absurds] *)

(** [absurds] applies to a goal [G] and replaces it with [(~ G) -> False].
    The expression [~ G] is simplified using [rew_logic].

    [absurds ;=> H] introduces [H] as the negation of the goal, and
    leaves [False] is the goal.

    [absurds_nosimpl] is similar, but it does not perform simplifications. *)

Lemma absurds_lemma : forall (G:Prop),
  ((~ G) -> False) ->
  G.
Proof using. intros. applys~ not_not_inv. Qed.

Ltac absurds_nosimpl_core tt :=
  applys absurds_lemma.

Tactic Notation "absurds_nosimpl" :=
  absurds_nosimpl_core tt.

Ltac absurds_post tt :=
  rew_logic.

Ltac absurds_core tt :=
  applys absurds_lemma;
  absurds_post tt.

Tactic Notation "absurds" :=
   absurds_core tt.


(* ********************************************************************** *)
(** * Predicate combinators, comparison and compatibility *)

(* ---------------------------------------------------------------------- *)
(** ** Definition of predicate combinators *)

Definition pred_true {A : Type} :=
  fun (_:A) => True.

Definition pred_false {A : Type} :=
  fun (_:A) => False.

Definition pred_not (A : Type) (P : A -> Prop) :=
  fun x => ~ (P x).

Definition pred_and (A : Type) (P Q : A -> Prop) :=
  fun x => P x /\ Q x.

Definition pred_or (A : Type) (P Q : A -> Prop) :=
  fun x => P x \/ Q x.

Definition pred_impl (A : Type) (P Q : A -> Prop) :=
  fun x => P x -> Q x.

#[global]
Hint Unfold pred_true pred_false.


(* ---------------------------------------------------------------------- *)
(** ** Properties of combinators *)

(* --LATER: reformulate using [pred_all] and [pred_and] (?) *)

Lemma pred_conj_forall_distrib : forall A (P Q: A->Prop),
  ((forall x, P x) /\ (forall x, Q x)) = (forall x, P x /\ Q x).
Proof using. intros. apply prop_ext. iff H. autos*. split; intros x; apply* (H x). Qed.


(* ---------------------------------------------------------------------- *)
(** ** Order on predicates *)

Definition pred_incl (A : Type) (P Q : A -> Prop) :=
  forall x, P x -> Q x.

(* --LATER: create a section here *)

Lemma pred_eq_forall_impl : forall A (P Q : A -> Prop),
  pred_incl P Q = (forall x, P x -> Q x).
Proof using. auto. Qed.

Lemma pred_incl_refl : forall A (P : A -> Prop),
  pred_incl P P.
Proof using. unfolds~ pred_incl. Qed.

Lemma pred_incl_trans : forall A (Q P R : A -> Prop),
  pred_incl P Q ->
  pred_incl Q R ->
  pred_incl P R.
Proof using. unfolds~ pred_incl. Qed.

Lemma pred_incl_antisym : forall A (P Q : A -> Prop),
  pred_incl P Q ->
  pred_incl Q P ->
  P = Q.
Proof using. extens*. Qed.

(** See also [LibRelation] and [LibOrder] for higher-level statements
    of these results *)



(* ********************************************************************** *)
(** * Existentials *)

(* ---------------------------------------------------------------------- *)
(** * Properties of unique existentials *)

(** [unique_st P x] asserts that [x] is the unique element for which
    [P x] holds. *)

Definition unique_st (A : Type) (P : A -> Prop) (x : A) :=
  P x /\ forall y, P y -> y = x.

#[global]
Hint Unfold unique_st.

(** [ex_unique P] asserts that there exists a unique element for which
    [P x] holds. *)

Definition ex_unique (A : Type) (P : A -> Prop) :=
  ex (unique_st P).

(** [exists! x, P] is the notation for [ex_unique P]. *)

Notation "'exists' ! x , P" := (ex_unique (fun x => P))
  (at level 200, x name, right associativity,
    format "'[' 'exists' !  '/  ' x ,  '/  ' P ']'") : type_scope.

Notation "'exists' ! x : A , P" :=
  (ex_unique (fun x:A => P))
  (at level 200, x name, right associativity,
    format "'[' 'exists' !  '/  ' x  :  A ,  '/  ' P ']'") : type_scope.

(** [at_most_one P] asserts that there exists at most one element for
    which [P x] holds. In other words, [P] has 0 or 1 inhabitant. *)

Definition at_most_one (A : Type) (P : A -> Prop) :=
  forall x y, P x -> P y -> x = y.

Section UniqueProp.
Variables (A : Type).
Implicit Types  (P : A -> Prop).

(** [exists! x, P] entails [exists x, P] *)

Lemma ex_of_ex_unique : forall P,
  ex_unique P ->
  ex P.
Proof using. introv (x&H&U). eauto. Qed.

(** [exists! x, P] entails [at_most_one P] *)

Lemma at_most_one_of_ex_unique : forall P,
  ex_unique P ->
  at_most_one P.
Proof using.
  introv (a&H&U) Px Py. applys~ eq_trans a. rewrite~ <- (U y).
Qed.

(** [exists x, P] and [at_most_one P] entail [exists! x, P] *)

Lemma ex_unique_of_ex_at_most_one : forall P,
  ex P ->
  at_most_one P ->
  ex_unique P.
Proof using. introv [x Px] H. exists x. split~. Qed.

End UniqueProp.


(* ********************************************************************** *)
(** * Conjunctions *)

(* ---------------------------------------------------------------------- *)
(** ** Changing the order of branches *)

Lemma conj_swap: forall (P Q: Prop),
  P ->
  Q ->
  Q /\ P.
Proof using. autos*. Qed.

Lemma conj_dup_r : forall P Q : Prop,
  Q ->
  (Q -> P) ->
  P /\ Q.
Proof using. autos*. Qed.

Lemma conj_dup_l : forall P Q : Prop,
  P ->
  (P -> Q) ->
  P /\ Q.
Proof using. autos*. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Parallel strengthening of a conjunction *)

Lemma conj_strengthen_2 : forall (Q1 Q2 P1 P2 : Prop),
  (Q1 /\ Q2) ->
  (Q1 -> P1) ->
  (Q2 -> P2) ->
  (P1 /\ P2).
Proof using. autos*. Qed.

Lemma conj_strengthen_3 : forall (Q1 Q2 Q3 P1 P2 P3 : Prop),
  (Q1 /\ Q2 /\ Q3) ->
  (Q1 -> P1) ->
  (Q2 -> P2) ->
  (Q3 -> P3) ->
  (P1 /\ P2 /\ P3).
Proof using. autos*. Qed.

Lemma conj_strengthen_4 : forall (Q1 Q2 Q3 Q4 P1 P2 P3 P4 : Prop),
  (Q1 /\ Q2 /\ Q3 /\ Q4) ->
  (Q1 -> P1) ->
  (Q2 -> P2) ->
  (Q3 -> P3) ->
  (Q4 -> P4) ->
  (P1 /\ P2 /\ P3 /\ P4).
Proof using. autos*. Qed.

Lemma conj_strengthen_5 : forall (Q1 Q2 Q3 Q4 Q5 P1 P2 P3 P4 P5 : Prop),
  (Q1 /\ Q2 /\ Q3 /\ Q4 /\ Q5) ->
  (Q1 -> P1) ->
  (Q2 -> P2) ->
  (Q3 -> P3) ->
  (Q4 -> P4) ->
  (Q5 -> P5) ->
  (P1 /\ P2 /\ P3 /\ P4 /\ P5).
Proof using. autos*. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Projections of lemmas concluding on a conjunction *)

Section ProjLemma.
Variables (A1 : Type).
Variables (A2 : forall (x1 : A1), Type).
Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).
Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).
Variables (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type).
Variables (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).
Variables (A7 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4) (x6 : A6 x5), Type).
Variables (A8 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4) (x6 : A6 x5) (x7 : A7 x6), Type).
Variables (A9 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4) (x6 : A6 x5) (x7 : A7 x6) (x8 : A8 x7), Type).
Variables (A10 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4) (x6 : A6 x5) (x7 : A7 x6) (x8 : A8 x7) (x9 : A9 x8), Type).
Variables (A11 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4) (x6 : A6 x5) (x7 : A7 x6) (x8 : A8 x7) (x9 : A9 x8) (x10 : A10 x9), Type).

Ltac prove_forall_conj_inv :=
  intros;
  match goal with H: context [_ /\ _] |- _ =>
    split; intros; apply H end.

Lemma forall_conj_inv_1 : forall (P Q : forall (x1:A1), Prop),
  (forall x1, P x1 /\ Q x1) ->
  (forall x1, P x1) /\
  (forall x1, Q x1).
Proof using. prove_forall_conj_inv. Qed.

Lemma forall_conj_inv_2 : forall (P Q : forall (x1:A1) (x2:A2 x1), Prop),
  (forall x1 x2, P x1 x2 /\ Q x1 x2) ->
  (forall x1 x2, P x1 x2) /\
  (forall x1 x2, Q x1 x2).
Proof using. prove_forall_conj_inv. Qed.

Lemma forall_conj_inv_3 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2), Prop),
  (forall x1 x2 x3, P x1 x2 x3 /\ Q x1 x2 x3) ->
  (forall x1 x2 x3, P x1 x2 x3) /\
  (forall x1 x2 x3, Q x1 x2 x3).
Proof using. prove_forall_conj_inv. Qed.

Lemma forall_conj_inv_4 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3), Prop),
  (forall x1 x2 x3 x4, P x1 x2 x3 x4 /\ Q x1 x2 x3 x4) ->
  (forall x1 x2 x3 x4, P x1 x2 x3 x4) /\
  (forall x1 x2 x3 x4, Q x1 x2 x3 x4).
Proof using. prove_forall_conj_inv. Qed.

Lemma forall_conj_inv_5 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4), Prop),
  (forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 /\ Q x1 x2 x3 x4 x5) ->
  (forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5) /\
  (forall x1 x2 x3 x4 x5, Q x1 x2 x3 x4 x5).
Proof using. prove_forall_conj_inv. Qed.

Lemma forall_conj_inv_6 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5), Prop),
  (forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 /\ Q x1 x2 x3 x4 x5 x6) ->
  (forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6) /\
  (forall x1 x2 x3 x4 x5 x6, Q x1 x2 x3 x4 x5 x6).
Proof using. prove_forall_conj_inv. Qed.

Lemma forall_conj_inv_7 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5) (x7:A7 x6), Prop),
  (forall x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7 /\ Q x1 x2 x3 x4 x5 x6 x7) ->
  (forall x1 x2 x3 x4 x5 x6 x7, P x1 x2 x3 x4 x5 x6 x7) /\
  (forall x1 x2 x3 x4 x5 x6 x7, Q x1 x2 x3 x4 x5 x6 x7).
Proof using. prove_forall_conj_inv. Qed.

Lemma forall_conj_inv_8 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5) (x7:A7 x6) (x8:A8 x7), Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8 /\ Q x1 x2 x3 x4 x5 x6 x7 x8) ->
  (forall x1 x2 x3 x4 x5 x6 x7 x8, P x1 x2 x3 x4 x5 x6 x7 x8) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8, Q x1 x2 x3 x4 x5 x6 x7 x8).
Proof using. prove_forall_conj_inv. Qed.

Lemma forall_conj_inv_9 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5) (x7:A7 x6) (x8:A8 x7) (x9:A9 x8), Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9) ->
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, P x1 x2 x3 x4 x5 x6 x7 x8 x9) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9, Q x1 x2 x3 x4 x5 x6 x7 x8 x9).
Proof using. prove_forall_conj_inv. Qed.

Lemma forall_conj_inv_10 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5) (x7:A7 x6) (x8:A8 x7) (x9:A9 x8) (x10:A10 x9), Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) ->
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10, Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10).
Proof using. prove_forall_conj_inv. Qed.

Lemma forall_conj_inv_11 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
 (x4:A4 x3) (x5:A5 x4) (x6:A6 x5) (x7:A7 x6) (x8:A8 x7) (x9:A9 x8) (x10:A10 x9) (x11:A11 x10), Prop),
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 /\ Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) ->
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, P x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11) /\
  (forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11, Q x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11).
Proof using. prove_forall_conj_inv. Qed.

End ProjLemma.

Arguments forall_conj_inv_1 [A1] [P] [Q].
Arguments forall_conj_inv_2 [A1] [A2] [P] [Q].
Arguments forall_conj_inv_3 [A1] [A2] [A3] [P] [Q].
Arguments forall_conj_inv_4 [A1] [A2] [A3] [A4] [P] [Q].
Arguments forall_conj_inv_5 [A1] [A2] [A3] [A4] [A5] [P] [Q].
Arguments forall_conj_inv_6 [A1] [A2] [A3] [A4] [A5] [A6] [P] [Q].
Arguments forall_conj_inv_7 [A1] [A2] [A3] [A4] [A5] [A6] [A7] [P] [Q].
Arguments forall_conj_inv_8 [A1] [A2] [A3] [A4] [A5] [A6] [A7] [A8] [P] [Q].
Arguments forall_conj_inv_9 [A1] [A2] [A3] [A4] [A5] [A6] [A7] [A8] [A9] [P] [Q].
Arguments forall_conj_inv_10 [A1] [A2] [A3] [A4] [A5] [A6] [A7] [A8] [A9] [A10] [P] [Q].
Arguments forall_conj_inv_11 [A1] [A2] [A3] [A4] [A5] [A6] [A7] [A8] [A9] [A10] [A11] [P] [Q].



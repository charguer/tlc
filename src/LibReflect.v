(**************************************************************************
* TLC: A library for Coq                                                  *
* Reflection between booleans and propositions                            *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics.
Require Export LibBool LibLogic.
Generalizable Variable P.


(* ********************************************************************** *)
(** * Reflection between booleans and propositions *)

(** [istrue b] produces a proposition that is [True] if and only if
    the boolean [b] is equal to [true].
    [isTrue P] produces a boolean expression that is [true] if and only
    if the proposition [P] is equal to [True]. *)

(* ---------------------------------------------------------------------- *)
(** ** Translation from booleans into propositions *)

(** Any boolean [b] can be viewed as a proposition through the
    relation [b = true]. *)

Coercion istrue (b : bool) : Prop := (b = true).

(** Specification of the coercion [istrue] *)

Lemma istrue_def : forall b,
  istrue b = (b = true).
Proof using. reflexivity. Qed.

Lemma istrue_true_eq : istrue true = True.
Proof using. rewrite istrue_def. extens*. Qed.

Lemma istrue_false_eq : istrue false = False.
Proof using. rewrite istrue_def. extens. iff; auto_false. Qed.

(** Update of the unfolding tactics to go through the coercion
    [istrue] (see LibTactics). *)

Ltac apply_to_head_of E cont ::=
  let go E := let P := get_head E in cont P in
  match E with
  | istrue ?A => go A
  | istrue (neg ?A) => go A
  | ?A = ?B => first [ go A | go B ]
  | ?A => go A
  end.

Global Opaque istrue.


(* ---------------------------------------------------------------------- *)
(** ** Tactics for proving boolean goals [true] and [false] *)

(** Proving the goals [true] and [~ false] *)

Lemma istrue_true : true.
Proof using. reflexivity. Qed.

Hint Resolve istrue_true.

Lemma istrue_not_false : ~ false.
Proof using. rewrite istrue_false_eq. intuition. Qed.

Hint Resolve istrue_not_false.

(** Proving the goal [false] and [False] *)

Lemma False_to_false : False -> false.
Proof using. intros K. false. Qed.

Hint Extern 1 (istrue false) =>
  apply False_to_false.

Lemma false_to_False : false -> False.
Proof using. intros K. rewrite~ istrue_false_eq in K. Qed.

Hint Extern 1 (False) => match goal with
  | H: istrue false |- _ => apply (istrue_not_false H) end.


(* ---------------------------------------------------------------------- *)
(** ** Translation from propositions into booleans *)

(** The expression [isTrue P] evaluates to [true] if and only if
    the proposition [P] is [True]. *)

Definition isTrue (P : Prop) : bool :=
  If P then true else false.

(** Simplification lemmas *)

Lemma isTrue_def : forall P,
  isTrue P = If P then true else false.
Proof using. reflexivity. Qed.

Lemma isTrue_True : isTrue True = true.
Proof using. unfolds. case_if; auto_false~. Qed.

Lemma isTrue_False : isTrue False = false.
Proof using. unfolds. case_if; auto_false~. Qed.

(** Notation for comparison in [bool] are [x '= y] and [x '<> y] *)

Notation "x ''=' y :> A" := (isTrue (@eq A x y))
  (at level 70, y at next level, only parsing) : comp_scope.
Notation "x ''<>' y :> A" := (isTrue (~ (@eq A x y)))
  (at level 69, y at next level, only parsing) : comp_scope.
Notation "x ''=' y" := (isTrue (@eq _ x y))
  (at level 70, y at next level, no associativity) : comp_scope.
Notation "x ''<>' y" := (isTrue (~ (@eq _ x y)))
  (at level 69, y at next level, no associativity) : comp_scope.

Global Opaque isTrue.
Open Scope comp_scope.


(* ---------------------------------------------------------------------- *)
(** ** Extensionality for boolean equality *)

Lemma bool_ext : forall b1 b2 : bool,
  (b1 <-> b2) -> b1 = b2.
Proof using.
  destruct b1; destruct b2; intros; auto_false.
  destruct H. false H; auto.
  destruct H. false H0; auto.
Qed.

Instance bool_extensional : Extensional bool.
Proof using. apply (@Build_Extensional bool iff bool_ext). Defined.


(* ********************************************************************** *)
(** * Lemmas for reflection *)

(* ---------------------------------------------------------------------- *)
(** ** Rewriting rules for distributing [istrue] *)

Section DistribIstrue.
Implicit Types b : bool.
Implicit Types P : Prop.

Lemma istrue_isTrue_iff : forall (P : Prop),
  istrue (isTrue P) <-> P.
Proof using. intros. rewrite isTrue_def. case_if; auto_false*. Qed.

Lemma istrue_isTrue : forall P,
  istrue (isTrue P) = P.
Proof using. extens. rewrite* istrue_isTrue_iff. Qed.

Lemma istrue_neg : forall b,
  istrue (!b) = ~ (istrue b).
Proof using. extens. tautob*. Qed.

Lemma istrue_and : forall b1 b2,
  istrue (b1 && b2) = (istrue b1 /\ istrue b2).
Proof using. extens. tautob*. Qed.

Lemma istrue_or : forall b1 b2,
  istrue (b1 || b2) = (istrue b1 \/ istrue b2).
Proof using. extens. tautob*. Qed.

End DistribIstrue.


(* ---------------------------------------------------------------------- *)
(** ** Rewriting rules for distributing [isTrue] *)

Section DistribIsTrue.
Implicit Types b : bool.
Implicit Types P : Prop.

Lemma isTrue_istrue : forall b,
  isTrue (istrue b) = b.
Proof using. extens. rewrite* istrue_isTrue_iff. Qed.

Lemma isTrue_not : forall P,
  isTrue (~ P) = ! isTrue P.
Proof using. extens. do 2 rewrite isTrue_def. do 2 case_if; auto_false*. Qed.

Lemma isTrue_and : forall P1 P2,
  isTrue (P1 /\ P2) = (isTrue P1 && isTrue P2).
Proof using. extens. do 3 rewrite isTrue_def. do 3 case_if; auto_false*. Qed.

Lemma isTrue_or : forall P1 P2,
  isTrue (P1 \/ P2) = (isTrue P1 || isTrue P2).
Proof using. extens. do 3 rewrite isTrue_def. do 3 case_if; auto_false*. Qed.

Lemma isTrue_if : forall P1 P2 P3,
  isTrue (If P1 then P2 else P3) = if isTrue P1 then isTrue P2 else isTrue P3.
Proof using.
  extens. do 4 rewrite isTrue_def.
  destruct (classicT P1).
    destruct* (classicT P2).
    destruct* (classicT P3).
Qed.

End DistribIsTrue.


(* ---------------------------------------------------------------------- *)
(** Corrolaries obtained by composition *)

Lemma istrue_neg_isTrue : forall P,
  istrue (! isTrue P) = ~ P.
Proof using. intros. rewrite istrue_neg. rewrite~ istrue_isTrue. Qed.

Lemma isTrue_not_istrue : forall b,
  isTrue (~ istrue b) = !b.
Proof using. intros. rewrite isTrue_not. rewrite~ isTrue_istrue. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Tactics for distributing [istrue] and [isTrue] *)

(* TODO: keep only one of [rew_refl] and [rew_reflect] *)

(** [rew_reflect] distributes [istrue]. *)

Hint Rewrite istrue_true_eq istrue_false_eq istrue_isTrue
  istrue_neg istrue_and istrue_or : rew_reflect.

Tactic Notation "rew_reflect" :=
  autorewrite with rew_reflect.
Tactic Notation "rew_reflect" "in" hyp(H) :=
  autorewrite with rew_reflect in H.
Tactic Notation "rew_reflect" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_reflect).
  (* autorewrite with rew_reflect in *. *)

Tactic Notation "rew_reflect" "~" :=
  rew_reflect; auto_tilde.
Tactic Notation "rew_reflect" "~" "in" hyp(H) :=
  rew_reflect in H; auto_tilde.
Tactic Notation "rew_reflect" "~" "in" "*" :=
  rew_reflect in *; auto_tilde.

Tactic Notation "rew_reflect" "*" :=
  rew_reflect; auto_star.
Tactic Notation "rew_reflect" "*" "in" hyp(H) :=
  rew_reflect in H; auto_star.
Tactic Notation "rew_reflect" "*" "in" "*" :=
  rew_reflect in *; auto_star.

(** [rew_unreflect] distributes [istrue]. *)

Hint Rewrite isTrue_True isTrue_False isTrue_istrue
 isTrue_not isTrue_and isTrue_or : rew_unreflect.

Tactic Notation "rew_unreflect" :=
  autorewrite with rew_unreflect.
Tactic Notation "rew_unreflect" "in" hyp(H) :=
  autorewrite with rew_unreflect in H.
Tactic Notation "rew_unreflect" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_unreflect).
  (* autorewrite with rew_unreflect in *. *)

Tactic Notation "rew_unreflect" "~" :=
  rew_unreflect; auto_tilde.
Tactic Notation "rew_unreflect" "~" "in" hyp(H) :=
  rew_unreflect in H; auto_tilde.
Tactic Notation "rew_unreflect" "~" "in" "*" :=
  rew_unreflect in *; auto_tilde.

Tactic Notation "rew_unreflect" "*" :=
  rew_unreflect; auto_star.
Tactic Notation "rew_unreflect" "*" "in" hyp(H) :=
  rew_unreflect in H; auto_star.
Tactic Notation "rew_unreflect" "*" "in" "*" :=
  rew_unreflect in *; auto_star.

(** [rew_refl] distributes [istrue] and [isTrue]
    and replaces [decide] with [isTrue]. *)

Hint Rewrite isTrue_True isTrue_False isTrue_istrue
 isTrue_not isTrue_and isTrue_or isTrue_if
 istrue_true_eq istrue_false_eq istrue_isTrue
 istrue_neg istrue_and istrue_or : rew_refl.

Tactic Notation "rew_refl" :=
  autorewrite with rew_refl.
Tactic Notation "rew_refl" "in" hyp(H) :=
  autorewrite with rew_refl in H.
Tactic Notation "rew_refl" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_refl).
  (* autorewrite with rew_refl in *. *)

Tactic Notation "rew_refl" "~" :=
  rew_refl; auto_tilde.
Tactic Notation "rew_refl" "~" "in" hyp(H) :=
  rew_refl in H; auto_tilde.
Tactic Notation "rew_refl" "~" "in" "*" :=
  rew_refl in *; auto_tilde.

Tactic Notation "rew_refl" "*" :=
  rew_refl; auto_star.
Tactic Notation "rew_refl" "*" "in" hyp(H) :=
  rew_refl in H; auto_star.
Tactic Notation "rew_refl" "*" "in" "*" :=
  rew_refl in *; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** Properties of boolean comparison *)

Lemma isTrue_true : forall (P:Prop),
  P -> 
  isTrue P = true.
Proof using. intros. rewrite isTrue_def. case_if*. Qed.

Lemma isTrue_false : forall (P:Prop),
  ~ P -> 
  isTrue P = false.
Proof using. intros. rewrite isTrue_def. case_if*. Qed.

Lemma eqb_eq : forall A (x y:A),
  x = y -> 
  (x '= y) = true.
Proof using. intros. subst. apply~ isTrue_true. Qed.

Lemma eqb_self : forall A (x:A),
  (x '= x) = true.
Proof using. intros. apply~ eqb_eq. Qed.

Lemma eqb_neq : forall A (x y:A),
  x <> y -> 
  (x '= y) = false.
Proof using. intros. subst. apply~ isTrue_false. Qed.

Lemma neqb_eq : forall A (x y:A),
  x = y -> 
  (x '<> y) = false.
Proof using. intros. subst. rewrite~ isTrue_false. Qed.

Lemma neqb_neq : forall A (x y:A),
  x <> y ->
  (x '<> y) = true.
Proof using. intros. subst. rewrite~ isTrue_true. Qed.

Lemma neqb_self : forall A (x:A),
  (x '<> x) = false.
Proof using. intros. apply~ neqb_eq. Qed.

Lemma eqb_sym : forall A (x y : A),
  (x '= y) = (y '= x).
Proof.
  introv. tests D: (x = y).
   rewrite~ eqb_self.
   do 2 rewrite~ eqb_neq.
Qed.


(* ********************************************************************** *)
(** * Tactics for reflection *)

(* ---------------------------------------------------------------------- *)
(** ** DEPRECATED  --- Tactic [fold_bool] *)

(** Tactic [fold_bool] simplifies goal and hypotheses of the form
    [b = true] and [b = false], as well as their symmetric *)

Section FoldingBool.
Variables (b : bool).

Lemma bool_eq_true :
  b -> b = true.
Proof using. auto. Qed.

Lemma eq_true_l :
  true = b -> b.
Proof using. tautob~. Qed.

Lemma eq_true_r :
  b = true -> b.
Proof using. tautob~. Qed.

Lemma eq_false_l :
  false = b -> !b.
Proof using. tautob~. Qed.

Lemma eq_false_r :
  b = false -> !b.
Proof using. tautob~. Qed.

Lemma eq_true_l_back :
  b -> true = b.
Proof using. tautob~. Qed.

Lemma eq_true_r_back :
  b -> b = true.
Proof using. tautob~. Qed.

Lemma eq_false_l_back :
  !b -> false = b.
Proof using. tautob~. Qed.

Lemma eq_false_r_back :
  !b -> b = false.
Proof using. tautob~. Qed.

Lemma eq_false_r_back_not :
  (~b) -> b = false.
Proof using. destruct b; auto_false. Qed. (*todo:tautob~.*)

Lemma neg_neg_back :
  b -> !!b.
Proof using. tautob~. Qed.

Lemma neg_neg_forward :
  !!b -> b.
Proof using. tautob~. Qed.

Lemma eq_bool_prove : forall b' : bool,
  (b -> b') -> (b' -> b) -> b = b'.
Proof using. lets: false_to_False. tautob~; tryfalse~. Qed.
  (* todo: simplify *)

Lemma eq_bool_iff : forall b' : bool,
  b = b' -> (b <-> b').
Proof using. tautob*. Qed.

End FoldingBool.

Ltac fold_bool :=
  repeat match goal with
  | H: true = ?b |- _ => applys_to H eq_true_l
  | H: ?b = true |- _ => applys_to H eq_true_r
  | H: false = ?b |- _ => applys_to H eq_false_l
  | H: ?b = false |- _ => applys_to H eq_false_r
  | H: istrue (!! ?b) |- _ => applys_to H neg_neg_forward
  | |- true = ?b => apply eq_true_l_back
  | |- ?b = true => apply eq_true_r_back
  | |- false = ?b => apply eq_false_l_back
  | |- ?b = false => apply eq_false_r_back
  | |- istrue (!! ?b) => apply neg_neg_back
  end.


(* ---------------------------------------------------------------------- *)
(** ** DEPRECATED --- Tactic [fold_prop] *)

(** Tactic [fold_prop] simplifies goal and hypotheses of the form
    [istrue b] or [~ istrue b], or [P = True] or [P = False]
    as well as their symmetric *)

Section FoldingProp.
Variables (P : Prop) (b : bool).

Lemma istrue_isTrue_back :
  P -> istrue (isTrue P).
Proof using. rewrite~ istrue_isTrue. Qed.

Lemma istrue_isTrue_forw :
  istrue (isTrue P) -> P.
Proof using. rewrite~ istrue_isTrue. Qed.

Lemma istrue_not_isTrue_back :
  ~ P -> istrue (! isTrue P).
Proof using. rewrite~ istrue_neg_isTrue. Qed.

Lemma istrue_not_isTrue_forw :
  istrue (! isTrue P) -> ~ P.
Proof using. rewrite~ istrue_neg_isTrue. Qed.

Lemma prop_eq_True_forw :
  (P = True) -> P.
Proof using. intros. subst~. Qed.

Lemma prop_eq_True_back :
  P -> (P = True).
Proof using. intros. extens*. Qed.

Lemma prop_eq_False_forw :
  (P = False) -> ~ P.
Proof using. intro. subst*. Qed.

Lemma prop_eq_False_back :
  ~ P -> (P = False).
Proof using. intros. extens*. Qed.

Lemma prop_neq_True_forw :
  (P <> True) -> ~ P.
Proof using. intros_all. apply H. extens*. Qed.

Lemma prop_neq_True_back :
  ~ P -> (P <> True).
Proof using. intros_all. subst~. Qed.

Lemma prop_neq_False_forw :
  (P <> False) -> P.
Proof using.
  intros_all. apply not_not_elim.
  intros_all. apply H. extens*.
Qed.

Lemma prop_neq_False_back :
  P -> (P <> False).
Proof using. introv M K. rewrite~ <- K. Qed.

Lemma not_istrue_isTrue_forw :
  ~ istrue (isTrue P) -> ~ P.
Proof using. apply contrapose_intro. rewrite~ istrue_isTrue. Qed.

Lemma not_istrue_not_isTrue_forw :
  ~ istrue (! isTrue P) -> P.
Proof using.
  rewrite <- (@not_not P). apply contrapose_intro.
  rewrite~ istrue_neg_isTrue.
Qed. (* todo: missing lemma from lib logic about ~A->B *)

Lemma not_istrue_isTrue_back :
  ~ P -> ~ istrue (isTrue P).
Proof using. apply contrapose_intro. rewrite~ istrue_isTrue. Qed.

Lemma not_istrue_not_isTrue_back :
  P -> ~ istrue (! isTrue P).
Proof using.
  rewrite <- (@not_not P). apply contrapose_intro.
  rewrite~ istrue_neg_isTrue.
Qed.

End FoldingProp.

Ltac fold_prop :=
  repeat match goal with
  | H: istrue (isTrue ?P) |- _ => applys_to H istrue_isTrue_forw
  | H: istrue (! isTrue ?P) |- _ => applys_to H istrue_not_isTrue_forw
  | H: ~ istrue (isTrue ?P) |- _ => applys_to H not_istrue_isTrue_forw
  | H: ~ istrue (! isTrue ?P) |- _ => applys_to H not_istrue_not_isTrue_forw
  | H: (?P = True) |- _ => applys_to H prop_eq_True_forw
  | H: (?P = False) |- _ => applys_to H prop_eq_False_forw
  | H: (True = ?P) |- _ => symmetry in H; applys_to H prop_eq_True_forw
  | H: (False = ?P) |- _ => symmetry in H; applys_to H prop_eq_False_forw
  | H: ~ (~ ?P) |- _ => applys_to H not_not_elim
  | |- istrue (isTrue ?P) => apply istrue_isTrue_back
  | |- istrue (! isTrue ?P) => apply istrue_not_isTrue_back
  | |- ~ istrue (isTrue ?P) => apply not_istrue_isTrue_back
  | |- ~ istrue (! isTrue ?P) => apply not_istrue_not_isTrue_back
  | |- (?P = True) => apply prop_eq_True_back
  | |- (?P = False) => apply prop_eq_False_back
  | |- (True = ?P) => symmetry; apply prop_eq_True_back
  | |- (False = ?P) => symmetry; apply prop_eq_False_back
  | |- ~ (~ ?P) => apply not_not_intro
  end.

  (* todo: improve case_if so that there is no need for that *)


(* ---------------------------------------------------------------------- *)
(** ** Tactics for case analysis on booleans *)

(** Extends the tactic [test_dispatch] from LibLogic.v, so as to
    be able to call the tactic [tests] directly on boolean expressions *)

Ltac tests_bool_base E H1 H2 :=
  tests_prop_base (istrue E) H1 H2.

Ltac tests_dispatch E H1 H2 ::=
  match type of E with
  | bool => tests_bool_base E H1 H2
  | Prop => tests_prop_base E H1 H2
  | {_}+{_} => tests_ssum_base E H1 H2
  end.


(* ---------------------------------------------------------------------- *)
(** ** Lemmas for testing booleans *)

Lemma bool_cases : forall (b : bool),
  b \/ !b.
Proof using. tautob*. Qed.

Lemma bool_cases_eq : forall (b : bool),
  b = true \/ b = false.
Proof using. tautob*. Qed.

Lemma xor_cases : forall (b1 b2 : bool),
  xor b1 b2 -> (b1 = true /\ b2 = false)
            \/ (b1 = false /\ b2 = true).
Proof using. tautob; auto_false*. Qed.

Implicit Arguments xor_cases [b1 b2].


(* ---------------------------------------------------------------------- *)
(** ** Tactic [logics] for normalizing bool/Prop coercions *)

Section Logics.

Implicit Type P : Prop.
Ltac isTrue_prove :=
  intros; try extens; try iff; rewrite isTrue_def in *; case_if; auto_false*.

Lemma true_eq_isTrue : forall P,
  (true = isTrue P) = P.
Proof using. isTrue_prove. Qed.

Lemma isTrue_eq_true : forall P,
  (isTrue P = true) = P.
Proof using. isTrue_prove. Qed.

Lemma false_eq_isTrue : forall P,
  (false = isTrue P) = ~ P.
Proof using. isTrue_prove. Qed.

Lemma isTrue_eq_false : forall P,
  (isTrue P = false) = ~ P.
Proof using. isTrue_prove. Qed.

Lemma not_not_eq : forall P,
  (~ ~ P) = P.
Proof using. intros. rew_logic*. Qed.

Lemma isTrue_eq_isTrue : forall P1 P2,
  (isTrue P1 = isTrue P2) = (P1 <-> P2).
Proof using.
  intros. extens. iff; repeat rewrite isTrue_def in *;
  repeat case_if; auto_false*.
Qed.

Lemma prop_eq_True : forall P,
  (P = True) = P.
Proof using. intros. rew_logic*. Qed.

Lemma prop_eq_False : forall P,
  (P = False) = ~ P.
Proof using. intro. rew_logic*. Qed.

Lemma prop_neq_True : forall P,
  (P <> True) = ~ P.
Proof using. intros. rew_logic*. Qed.

Lemma prop_neq_False : forall P,
  (P <> False) = P.
Proof using.
  intro. rew_logic*. iff.
  apply not_not_elim. intros E. apply H. autos*.
  intros E. rewrite* <- E.
Qed.

End Logics.

Hint Rewrite
  true_eq_isTrue isTrue_eq_true
  false_eq_isTrue isTrue_eq_false
  isTrue_eq_isTrue not_not_eq
  istrue_true_eq istrue_false_eq istrue_isTrue
  istrue_neg istrue_and istrue_or
  : rew_isTrue.

Ltac rew_isTrue :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_isTrue).

Tactic Notation "logics" :=
  rew_isTrue.
Tactic Notation "logics" "~" :=
  logics; auto_tilde.
Tactic Notation "logics" "*" :=
  logics; auto_star.

(* TODO: should export "rew_isTrue" as a name, not "logics" *)


(* ---------------------------------------------------------------------- *)
(** ** Tactics extended for reflection *)

(* Extension of [extens] *)

Ltac extens_base :=
  first [ extens_core | intros; extens_core ]; logics.

(* Extension of [case_if] *)

Ltac case_if_post ::= logics; tryfalse.

(* Extension of [absurds] *)

Ltac absurds_post H :=
  rew_logic in H.






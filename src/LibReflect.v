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
Open Scope comp_scope.

Global Opaque isTrue.



(* ---------------------------------------------------------------------- *)
(** ** Extensionality for boolean equality *)

Lemma bool_ext : forall (b1 b2 : bool),
  (b1 <-> b2) -> b1 = b2.
Proof using.
  destruct b1; destruct b2; intros; auto_false.
  destruct H. false H; auto.
  destruct H. false H0; auto.
Qed.

Lemma bool_ext_eq : forall (b1 b2 : bool),
  (b1 = b2) = (b1 <-> b2).
Proof using.
  intros. extens. iff M. { subst*. } { applys* bool_ext. }
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
Proof using. extens. tautob. Qed.

Lemma istrue_and : forall b1 b2,
  istrue (b1 && b2) = (istrue b1 /\ istrue b2).
Proof using. extens. tautob. Qed.

Lemma istrue_or : forall b1 b2,
  istrue (b1 || b2) = (istrue b1 \/ istrue b2).
Proof using. extens. tautob. Qed.

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
(** ** Lemmas for testing booleans *)

Lemma bool_cases : forall (b : bool),
  b \/ !b.
Proof using. tautob. Qed.

Lemma bool_cases_eq : forall (b : bool),
  b = true \/ b = false.
Proof using. tautob. Qed.

Lemma xor_cases : forall (b1 b2 : bool),
  xor b1 b2 -> 
     (b1 = true /\ b2 = false)
  \/ (b1 = false /\ b2 = true).
Proof using. tautob; auto_false*. Qed.

Arguments xor_cases [b1] [b2].


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

(** [rew_unreflect] distributes [isTrue]. *)

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
(** * Tactics *)

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

Lemma isTrue_eq_isTrue : forall P1 P2,
  (isTrue P1 = isTrue P2) = (P1 <-> P2).
Proof using.
  intros. extens. iff; repeat rewrite isTrue_def in *;
  repeat case_if; auto_false*.
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

(** Extension of the tactic [case_if] to automatically performs
    simplification using [logics]. *)

Ltac case_if_post ::= logics; tryfalse.

(** Extension of the tactic [test_dispatch] from LibLogic.v, so as to
    be able to call the tactic [tests] directly on boolean expressions *)

Ltac tests_bool_base E H1 H2 :=
  tests_prop_base (istrue E) H1 H2.

Ltac tests_dispatch E H1 H2 ::=
  match type of E with
  | bool => tests_bool_base E H1 H2
  | Prop => tests_prop_base E H1 H2
  | {_}+{_} => tests_ssum_base E H1 H2
  end.

(** Extension of the tactic [apply_to_head_of] (see LibTactics). *)

Ltac apply_to_head_of E cont ::=
  let go E := let P := get_head E in cont P in
  match E with
  | istrue ?A => go A
  | istrue (neg ?A) => go A
  | ?A = ?B => first [ go A | go B ]
  | ?A => go A
  end.



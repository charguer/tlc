(**************************************************************************
* TLC: A library for Coq                                                  *
* Reflection between booleans and propositions                            *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics.
From TLC Require Export LibBool LibLogic.

Implicit Type P : Prop.
Implicit Type b : bool.


(* ********************************************************************** *)
(** * Reflection between booleans and propositions *)

(** - [istrue b] produces a proposition that is [True] if and only if
      the boolean [b] is equal to [true].

    - [isTrue P] produces a boolean expression that is [true] if and only
      if the proposition [P] is equal to [True]. *)

(* ---------------------------------------------------------------------- *)
(** ** Translation from booleans into propositions *)

(** Any boolean [b] can be viewed as a proposition through the
    relation [b = true]. *)

Coercion istrue (b : bool) : Prop := (b = true).

(** Specification *)

Lemma istrue_eq_eq_true : forall b,
  istrue b = (b = true).
Proof using. reflexivity. Qed.

Lemma istrue_true_eq :
  istrue true = True.
Proof using. rewrite istrue_eq_eq_true. extens*. Qed.

Lemma istrue_false_eq :
  istrue false = False.
Proof using. rewrite istrue_eq_eq_true. extens. iff; auto_false. Qed.

Global Opaque istrue.

(** Proving the goals [true] and [~ false] *)

Lemma istrue_true : istrue true. (* [true] *)
Proof using. reflexivity. Qed.

Lemma not_istrue_false : ~ (istrue false). (* ~ false. *)
Proof using. rewrite istrue_false_eq. intuition. Qed.

(** Equivalence of [false] and [False] *)

Lemma false_of_False :
  False ->
  false.
Proof using. intros K. false. Qed.

Lemma False_of_false :
  false ->
  False.
Proof using. intros K. rewrite~ istrue_false_eq in K. Qed.

(** Hints for proving [false] and [False] *)

#[global]
Hint Resolve istrue_true not_istrue_false.

#[global]
Hint Extern 1 (istrue false) =>
  apply false_of_False.

#[global]
Hint Extern 1 (False) => match goal with
  | H: istrue false |- _ => apply (not_istrue_false H) end.


(* ---------------------------------------------------------------------- *)
(** ** Translation from propositions into booleans *)

(** The expression [isTrue P] evaluates to [true] if and only if
    the proposition [P] is [True]. *)

Definition isTrue (P : Prop) : bool :=
  If P then true else false.

(** Specification *)

Lemma isTrue_eq_if : forall P,
  isTrue P = If P then true else false.
Proof using. reflexivity. Qed.

Lemma isTrue_True :
  isTrue True = true.
Proof using. unfolds. case_if; auto_false~. Qed.

Lemma isTrue_False :
  isTrue False = false.
Proof using. unfolds. case_if; auto_false~. Qed.

Global Opaque isTrue.

(** Lemmas *)

Lemma isTrue_eq_true : forall P,
  P ->
  isTrue P = true.
Proof using. intros. rewrite isTrue_eq_if. case_if*. Qed.

Lemma isTrue_eq_false : forall P,
  ~ P ->
  isTrue P = false.
Proof using. intros. rewrite isTrue_eq_if. case_if*. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Extensionality for boolean equality, stated using [istrue] *)

Lemma bool_ext : forall b1 b2,
  (b1 <-> b2) ->
  b1 = b2.
Proof using.
  destruct b1; destruct b2; intros; auto_false.
  destruct H. false H; auto.
  destruct H. false H0; auto.
Qed.

Lemma bool_ext_eq : forall b1 b2,
  (b1 = b2) = (b1 <-> b2).
Proof using.
  intros. extens. iff M. { subst*. } { applys* bool_ext. }
Qed.

#[global]
Instance Extensionality_bool : Extensionality bool.
Proof using. apply (Extensionality_make bool_ext). Defined.


(* ---------------------------------------------------------------------- *)
(** ** Specification of boolean equality *)

(** [isTrue_pred p P] asserts that [p] is a boolean function that implements
    the predicate [P], in the sense that [p x] returns [true] iff [P x] holds. *)

Definition isTrue_pred A (p:A->bool) (P:A->Prop) : Prop :=
  forall x, p x = isTrue (P x).

(** [is_beq f] asserts that [f] is a boolean comparison function
    that implements logical equality: [f x y] returns [true] iff
    [x = y]. *)

Definition is_beq A (f:A->A->bool) :=
  forall x y, f x y = isTrue (x = y).


(* ********************************************************************** *)
(** * Rewriting rules *)

(* ---------------------------------------------------------------------- *)
(** ** Rewriting rules for distributing [istrue] *)

Lemma istrue_isTrue_eq : forall P,
  istrue (isTrue P) = P.
Proof using. extens. rewrite isTrue_eq_if. case_if; auto_false*. Qed.

Lemma istrue_neg_eq : forall b,
  istrue (!b) = ~ (istrue b).
Proof using. extens. tautob. Qed.

Lemma istrue_and_eq : forall b1 b2,
  istrue (b1 && b2) = (istrue b1 /\ istrue b2).
Proof using. extens. tautob. Qed.

Lemma istrue_or_eq : forall b1 b2,
  istrue (b1 || b2) = (istrue b1 \/ istrue b2).
Proof using. extens. tautob. Qed.

(** Corollary *)

Lemma istrue_neg_isTrue : forall P,
  istrue (! isTrue P) = ~ P.
Proof using. intros. rewrite istrue_neg_eq. rewrite~ istrue_isTrue_eq. Qed.

(** [istrue] and conditionals *)

Lemma If_istrue : forall b A (x y : A),
    (If istrue b then x else y)
  = (if b then x else y).
Proof using. intros. case_if as C; case_if as D; auto. Qed.

Lemma istrue_If_eq : forall P b1 b2,
    istrue (If P then b1 else b2)
  = (If P then istrue b1 else istrue b2).
Proof using. extens. case_if*. Qed.

Lemma istrue_if_eq : forall b1 b2 b3,
    istrue (if b1 then b2 else b3)
  = (If istrue b1 then istrue b2 else istrue b3).
Proof using. intros. do 2 case_if; auto. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Rewriting rules for distributing [isTrue] *)

Lemma isTrue_istrue : forall b,
  isTrue (istrue b) = b.
Proof using. extens. rewrite* istrue_isTrue_eq. Qed.

Lemma isTrue_not : forall P,
  isTrue (~ P) = ! isTrue P.
Proof using. extens. do 2 rewrite isTrue_eq_if. do 2 case_if; auto_false*. Qed.

Lemma isTrue_and : forall P1 P2,
  isTrue (P1 /\ P2) = (isTrue P1 && isTrue P2).
Proof using. extens. do 3 rewrite isTrue_eq_if. do 3 case_if; auto_false*. Qed.

Lemma isTrue_or : forall P1 P2,
  isTrue (P1 \/ P2) = (isTrue P1 || isTrue P2).
Proof using. extens. do 3 rewrite isTrue_eq_if. do 3 case_if; auto_false*. Qed.

(** Corollary *)

Lemma isTrue_not_istrue : forall b,
  isTrue (~ istrue b) = !b.
Proof using. intros. rewrite isTrue_not. rewrite~ isTrue_istrue. Qed.

(** Simplification of equalities involving isTrue *)

Section IsTrueEqualities.

Ltac prove_isTrue_lemma :=
  intros; try extens; try iff; rewrite isTrue_eq_if in *; case_if; auto_false*.

Lemma true_eq_isTrue_eq : forall P,
  (true = isTrue P) = P.
Proof using. prove_isTrue_lemma. Qed.

Lemma isTrue_eq_true_eq : forall P,
  (isTrue P = true) = P.
Proof using. prove_isTrue_lemma. Qed.

Lemma false_eq_isTrue_eq : forall P,
  (false = isTrue P) = ~ P.
Proof using. prove_isTrue_lemma. Qed.

Lemma isTrue_eq_false_eq : forall P,
  (isTrue P = false) = ~ P.
Proof using. prove_isTrue_lemma. Qed.

Lemma isTrue_eq_isTrue_eq : forall P1 P2,
  (isTrue P1 = isTrue P2) = (P1 <-> P2).
Proof using.
  intros. extens. iff; repeat rewrite isTrue_eq_if in *;
  repeat case_if; auto_false*.
Qed.

End IsTrueEqualities.

(** [isTrue] and conditionals *)

Lemma if_isTrue : forall P A (x y : A),
    (if isTrue P then x else y)
  = (If P then x else y).
Proof using.
  intros. case_if as C; case_if as D; auto.
  { rewrite* isTrue_eq_true_eq in C. }
  { rewrite* isTrue_eq_false_eq in C. }
Qed.

Lemma isTrue_If : forall P1 P2 P3,
    isTrue (If P1 then P2 else P3)
  = If P1 then isTrue P2 else isTrue P3.
Proof using. extens. case_if*. Qed.

Lemma isTrue_If_eq_if_isTrue : forall P1 P2 P3,
    isTrue (If P1 then P2 else P3)
  = (if isTrue P1 then isTrue P2 else isTrue P3).
Proof using. intros. rewrite if_isTrue. rewrite~ isTrue_If. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Lemmas for testing booleans *)

Lemma bool_inv_or : forall b,
  b \/ !b.
Proof using. tautob. Qed.

Lemma bool_inv_or_eq : forall b,
  b = true \/ b = false.
Proof using. tautob. Qed.

Lemma xor_inv_or : forall b1 b2,
  xor b1 b2 ->
     (b1 = true /\ b2 = false)
  \/ (b1 = false /\ b2 = true).
Proof using. tautob; auto_false*. Qed.

Arguments xor_inv_or [b1] [b2].


(* ---------------------------------------------------------------------- *)
(** ** Lemmas for normalizing [b = true] and [b = false] terms *)

Lemma bool_eq_true_eq : forall b,
  (b = true) = istrue b.
Proof using. extens. tautob. Qed.

Lemma bool_eq_false_eq : forall b,
  (b = false) = istrue (!b).
Proof using. extens. tautob. Qed.

Lemma true_eq_bool_eq : forall b,
  (true = b) = istrue b.
Proof using. extens. tautob. Qed.

Lemma false_eq_bool_eq : forall b,
  (false = b) = istrue (!b).
Proof using. extens. tautob. Qed.


(* ********************************************************************** *)
(** * Tactics *)

(* ---------------------------------------------------------------------- *)
(** ** Tactics [rew_istrue] to distribute [istrue] *)

(** [rew_istrue] distributes [istrue]. It is useful to replace all
    boolean operators with corresponding logical operators. *)

#[global]
Hint Rewrite istrue_true_eq istrue_false_eq istrue_isTrue_eq
  istrue_neg_eq istrue_and_eq istrue_or_eq
  If_istrue istrue_If_eq istrue_if_eq: rew_istrue.

Tactic Notation "rew_istrue" :=
  autorewrite with rew_istrue.
Tactic Notation "rew_istrue" "in" hyp(H) :=
  autorewrite with rew_istrue in H.
Tactic Notation "rew_istrue" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_istrue).
  (* autorewrite with rew_istrue in *. *)

Tactic Notation "rew_istrue" "~" :=
  rew_istrue; auto_tilde.
Tactic Notation "rew_istrue" "~" "in" hyp(H) :=
  rew_istrue in H; auto_tilde.
Tactic Notation "rew_istrue" "~" "in" "*" :=
  rew_istrue in *; auto_tilde.

Tactic Notation "rew_istrue" "*" :=
  rew_istrue; auto_star.
Tactic Notation "rew_istrue" "*" "in" hyp(H) :=
  rew_istrue in H; auto_star.
Tactic Notation "rew_istrue" "*" "in" "*" :=
  rew_istrue in *; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** Tactics [rew_isTrue] to distribute [isTrue] *)

(** [rew_isTrue] distributes [isTrue].
    This tactic is probably much less useful than [rew_istrue], since logical
    operators are often simpler to work with. *)

#[global]
Hint Rewrite isTrue_True isTrue_False isTrue_istrue
  isTrue_not isTrue_and isTrue_or
  if_isTrue isTrue_If : rew_isTrue.

Tactic Notation "rew_isTrue" :=
  autorewrite with rew_isTrue.
Tactic Notation "rew_isTrue" "in" hyp(H) :=
  autorewrite with rew_isTrue in H.
Tactic Notation "rew_isTrue" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_isTrue).
  (* autorewrite with rew_isTrue in *. *)

Tactic Notation "rew_isTrue" "~" :=
  rew_isTrue; auto_tilde.
Tactic Notation "rew_isTrue" "~" "in" hyp(H) :=
  rew_isTrue in H; auto_tilde.
Tactic Notation "rew_isTrue" "~" "in" "*" :=
  rew_isTrue in *; auto_tilde.

Tactic Notation "rew_isTrue" "*" :=
  rew_isTrue; auto_star.
Tactic Notation "rew_isTrue" "*" "in" hyp(H) :=
  rew_isTrue in H; auto_star.
Tactic Notation "rew_isTrue" "*" "in" "*" :=
  rew_isTrue in *; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** Tactics useful for program verification, when reasoning about
       the result of if-statements over boolean expressions, i.e.
       an expression of the form [b = ..] or [.. = b], which produces
       hypotheses of the form [true = ..] and [false = ..] or symmetric.
       It is used as post-treatment for tactic [case_if]. *)

#[global]
Hint Rewrite
  true_eq_isTrue_eq isTrue_eq_true_eq
  false_eq_isTrue_eq isTrue_eq_false_eq
  isTrue_eq_isTrue_eq
  not_not_eq
  istrue_true_eq istrue_false_eq istrue_isTrue_eq
  istrue_neg_eq istrue_and_eq istrue_or_eq
  bool_eq_true_eq bool_eq_false_eq true_eq_bool_eq false_eq_bool_eq
  : rew_bool_eq.

Tactic Notation "rew_bool_eq" :=
  autorewrite with rew_bool_eq.
Tactic Notation "rew_bool_eq" "~" :=
  rew_bool_eq; auto_tilde.
Tactic Notation "rew_bool_eq" "*" :=
  rew_bool_eq; auto_star.

Tactic Notation "rew_bool_eq" "in" hyp(H) :=
  autorewrite with rew_bool_eq in H.
Tactic Notation "rew_bool_eq" "~" "in" hyp(H) :=
  rew_bool_eq in H; auto_tilde.
Tactic Notation "rew_bool_eq" "*" "in" hyp(H) :=
  rew_bool_eq in H; auto_star.

Tactic Notation "rew_bool_eq" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_bool_eq).
  (* autorewrite with rew_bool_eq in *. *)
Tactic Notation "rew_bool_eq" "~" "in" "*" :=
  rew_bool_eq in *; auto_tilde.
Tactic Notation "rew_bool_eq" "*" "in" "*" :=
  rew_bool_eq in *; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** Tactics extended for reflection *)

(** Extension of the tactic [case_if] to automatically performs
    simplification using [logics].

    For less aggressive introduction of [istrue], consider rewriting
    without the lemmas:
    [bool_eq_true_eq bool_eq_false_eq true_eq_bool_eq false_eq_bool_eq]
*)

Ltac case_if_post H ::=
  rew_bool_eq in H; tryfalse.

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


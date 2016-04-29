(**************************************************************************
* TLC: A library for Coq                                                  *
* Epsilon operator                                                        *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic.
Generalizable Variables A B.


(* ********************************************************************** *)
(** * Definition and specification of Hilbert's epsilon operator *)

(* ---------------------------------------------------------------------- *)
(** ** Construction of epsilon *)

(* TODO: inline the lemma? *)
Lemma Inhab_witness : forall `{Inhab A}, { x : A | True }.
Proof using. intros. destruct H as [H]. apply~ indefinite_description. Qed.

Lemma epsilon_def : forall `{Inhab A} (P : A->Prop),
  { x : A | (exists y, P y) -> P x }.
Proof using.
  intros A I P. destruct (classicT (exists y, P y)) as [H|H].
    apply indefinite_description. destruct H. exists~ x.
    destruct (@Inhab_witness _ I) as [x _].
     exists x. auto_false~.
Qed.

Definition epsilon `{Inhab A} (P : A -> Prop) : A
  := proj1_sig (epsilon_def P).

(* ---------------------------------------------------------------------- *)
(** ** Specification of epsilon *)

Lemma epsilon_spec_exists : forall `{Inhab A} (P : A->Prop),
  (exists x, P x) -> P (epsilon P).
Proof using. intros. apply~ (proj2_sig (epsilon_def P)). Qed.

Lemma epsilon_elim_exists : forall `{Inhab A} (P Q : A->Prop),
  (exists x, P x) -> (forall x, P x -> Q x) -> Q (epsilon P).
Proof using. introv E M. apply M. apply~ epsilon_spec_exists. Qed.

Lemma epsilon_spec : forall `{Inhab A} (P : A->Prop) x,
  P x -> P (epsilon P).
Proof using. intros. apply* (epsilon_spec_exists). Qed.

Lemma epsilon_elim : forall `{Inhab A} (P Q : A->Prop) x,
  P x -> (forall x, P x -> Q x) -> Q (epsilon P).
Proof using. introv Px W. apply W. apply* epsilon_spec_exists. Qed.

Lemma epsilon_eq : forall A {I:Inhab A} (P P':A->Prop),
  (forall x, P x <-> P' x) ->
  epsilon P = epsilon P'.
Proof using. introv H. fequals. apply~ prop_ext_1. Qed.

(* ---------------------------------------------------------------------- *)
(** ** Tactics to work with [epsilon] *)

(* TODO: comment and demos *)

Lemma epsilon_spec' : forall A (P:A->Prop) (x:A),
  forall (H:P x) {IA:Inhab A}, P (epsilon P).
Proof using. intros. applys* epsilon_spec. Qed.

Lemma epsilon_spec_exists' : forall A (P : A->Prop) {IA:Inhab A},
  (exists x, P x) -> P (epsilon P).
Proof using. intros. applys* epsilon_spec_exists. Qed.

Ltac find_epsilon cont :=
  match goal with
  | |- context [epsilon ?E] => cont E
  | H: context [epsilon ?E] |- _ => cont E
  end.

Ltac find_epsilon_in H cont :=
  match type of H with context [epsilon ?E] => cont E end.

Ltac spec_epsilon_post E X W I :=
   first [ lets I: (>> (@epsilon_spec' _ E W) __ __)
         | lets I: (>> (@epsilon_spec' _ E _ W) __)  ];
   [ | sets X: (epsilon E) ].

Ltac spec_epsilon_exists_post E X I :=
   lets I: (>> (@epsilon_spec_exists' _ E) __ __); [ | sets X: (epsilon E) ].

Tactic Notation "sets_epsilon" "as" ident(X) :=
  find_epsilon ltac:(fun E => sets X: (epsilon E)).

Tactic Notation "sets_epsilon" "in" hyp(H) "as" ident(X) :=
  find_epsilon_in H ltac:(fun E => sets X: (epsilon E)).

Tactic Notation "spec_epsilon" constr(W) "as" ident(X) simple_intropattern(I) :=
  find_epsilon ltac:(fun E => spec_epsilon_post E X W I).

Tactic Notation "spec_epsilon" constr(W) "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  find_epsilon_in H ltac:(fun E => spec_epsilon_post E X W I).

Tactic Notation "spec_epsilon" "as" ident(X) simple_intropattern(I) :=
  find_epsilon ltac:(fun E => spec_epsilon_exists_post E X I).
Tactic Notation "spec_epsilon" "as" ident(X) :=
  let H := fresh "H" X in spec_epsilon as X H.

Tactic Notation "spec_epsilon" "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  find_epsilon_in H ltac:(fun E => spec_epsilon_exists_post E X I).
Tactic Notation "spec_epsilon" "in" hyp(H) "as" ident(X) :=
  let H := fresh "H" X in spec_epsilon in H as X H.

Tactic Notation "spec_epsilon" "~" constr(W) "as" ident(X) simple_intropattern(I) :=
  spec_epsilon W as X I; auto_tilde.
Tactic Notation "spec_epsilon" "~" constr(W) "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  spec_epsilon W in H as X I; auto_tilde.
Tactic Notation "spec_epsilon" "~" "as" ident(X) simple_intropattern(I) :=
  spec_epsilon as X I; auto_tilde.
Tactic Notation "spec_epsilon" "~" "as" ident(X) :=
  spec_epsilon as X; auto_tilde.
Tactic Notation "spec_epsilon" "~" "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  spec_epsilon in H as X I; auto_tilde.
Tactic Notation "spec_epsilon" "~" "in" hyp(H) "as" ident(X) :=
  spec_epsilon in H as X; auto_tilde.

Tactic Notation "spec_epsilon" "*" constr(W) "as" ident(X) simple_intropattern(I) :=
  spec_epsilon W as X I; auto_star.
Tactic Notation "spec_epsilon" "*" constr(W) "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  spec_epsilon W in H as X I; auto_star.
Tactic Notation "spec_epsilon" "*" "as" ident(X) simple_intropattern(I) :=
  spec_epsilon as X I; auto_star.
Tactic Notation "spec_epsilon" "*" "as" ident(X) :=
  spec_epsilon as X; auto_star.
Tactic Notation "spec_epsilon" "*" "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  spec_epsilon in H as X I; auto_star.
Tactic Notation "spec_epsilon" "*" "in" hyp(H) "as" ident(X) :=
  spec_epsilon in H as X; auto_star.


(* ********************************************************************** *)
(** * Conversion from relations to functions *)

Section Choose.

(* Let [R] be an arbitrary binary relation at type [A -> B -> Prop]. *)

Variable A B : Type.
Variable R : A -> B -> Prop.
Context `{IB:Inhab B}.

(* We turn it into a function, which ostensibly is a total function of type
   [A -> B], but in reality is well-defined only in the domain of [R]. *)

Definition choose (a : A) : B :=
  epsilon (fun b => R a b).

(* TODO choose_spec and choose_unique could be reformulated using
   incl_fr and incl_rf *)

(* Every [a] in the domain of [R] is related by [R] with [choose a]. *)

Lemma choose_spec:
  forall a,
  ~ (forall b, ~ R a b) ->
  R a (choose a).
Proof using IB.
  intros.
  (* Since [a] is not a root, it has a parent [b]. *)
  forwards [ b ? ]: exists_from_not. eauto.
  (* By definition of [choose], there follows that [choose a] is
     well-defined, hence there is an edge from [a] to [choose a]. *)
  unfold choose. eapply epsilon_spec. eauto.
Qed.

(* If the relation [R] is functional, then [choose a] is unique.
   The existence of an edge from [a] to [b] implies that [b] is
   [choose a]. *)

Variable functional_R:
  forall a b1 b2, R a b1 -> R a b2 -> b1 = b2.
  (* TODO: use a definition of functional, and inline in the lemma below *)

Lemma choose_unique:
  forall a b,
  R a b ->
  choose a = b.
Proof using IB functional_R.
  intros.
  (* [R a b] implies that [a] is in the domain of [R].
     Hence there is an edge from [a] to [choose a]. *)
  forwards: choose_spec. rewrite not_forall_not. eauto.
  (* The result follows from the hypothesis that [R] is functional. *)
  eauto.
Qed.

End Choose.

(* In the special case where [B] is [A], the inhabitation witness
   can be constructed out of [a]. *)

Definition choose_ A (R : A -> A -> Prop) (a : A) : A :=
  @choose A A R (prove_Inhab a) a.
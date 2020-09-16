(**************************************************************************
* TLC: A library for Coq                                                  *
* Epsilon operator                                                        *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibRelation.
Generalizable Variables A B.


(* ********************************************************************** *)
(** * Definition and specification of Hilbert's epsilon operator *)

(* ---------------------------------------------------------------------- *)
(** ** Definition of epsilon *)

(** [epsilon P] where [P] is a predicate over an inhabited type [A],
    returns a value [x] of type [A] that satisfies [P], if there exists
    one such value, else it returns an arbitrary value of type [A]. *)

Definition epsilon_def : forall A {IA:Inhab A} (P:A->Prop),
  { x : A | (exists y, P y) -> P x }.
Proof using.
  intros A IA P. destruct (classicT (exists y, P y)) as [H|H].
  { apply indefinite_description. destruct H as [x H].
    exists x. intros _. apply H. }
  { exists (@arbitrary A IA). intros N. false H. apply N. }
Qed.

Definition epsilon A {IA: Inhab A} (P:A->Prop) : A :=
  sig_val (epsilon_def P).

Lemma pred_epsilon : forall A {IA:Inhab A} (P:A->Prop),
  (exists x, P x) ->
  P (epsilon P).
Proof using. intros. apply~ (sig_proof (epsilon_def P)). Qed.

Opaque epsilon.

(* Remark: the proof term associated with the definition *)

Definition epsilon_def' A {IA:Inhab A} (P:A->Prop) :
  { x : A | (exists y, P y) -> P x } :=
  match classicT (exists y, P y) with
  | left H =>
      indefinite_description
        (let (x,H0) := H in
         ex_intro (fun x0 => (exists y, P y) -> P x0)
                   x
                  (fun N => H0))
  | right H =>
      exist (fun x => (exists y, P y) -> P x)
            arbitrary
            (fun N => False_ind (P arbitrary) (H N))
  end.


(* ---------------------------------------------------------------------- *)
(** ** Lemmas about epsilon *)

Lemma pred_epsilon_weaken : forall A {IA:Inhab A} (P Q : A->Prop),
  (exists x, P x) ->
  (forall x, P x -> Q x) ->
  Q (epsilon P).
Proof using. introv E M. apply M. apply* pred_epsilon. Qed.

Lemma pred_epsilon_of_val : forall A (x:A) (P:A->Prop) {IA:Inhab A},
  P x ->
  P (epsilon P).
Proof using. intros. apply* pred_epsilon. Qed.

Lemma pred_epsilon_of_val_weaken : forall A (x:A) (P Q:A->Prop) {IA:Inhab A},
  P x ->
  (forall x, P x -> Q x) ->
  Q (epsilon P).
Proof using. introv Px W. apply W. apply* pred_epsilon. Qed.

Lemma epsilon_eq : forall A {IA:Inhab A} (P Q:A->Prop),
  (forall x, P x <-> Q x) ->
  epsilon P = epsilon Q.
Proof using. introv H. fequals. extens*. Qed.


(* ---------------------------------------------------------------------- *)
(** ** (Private) tactic [epsilon_find] *)

(** [epsilon_find cont] locates an expression of the form [epsilon P]
    in the goal and invokes the continuation [cont] on [P].

    [epsilon_find_in H cont] is similar but looks for the expression
    only in the hypothesis named [H]. *)

Ltac epsilon_find cont :=
  match goal with
  | |- context [epsilon ?P] => cont P
  | H: context [epsilon ?P] |- _ => cont P
  end.

Ltac epsilon_find_in H cont :=
  match type of H with context [epsilon ?P] => cont P end.


(* ---------------------------------------------------------------------- *)
(** ** Tactics [epsilon_name] *)

(** [epsilon_name X] assigns a name [X] to an expression of the
    form [epsilon P] that appears in the goal or an hypothesis,
    by calling [set (X := epsilon P)].

    [epsilon_name X in H] assignes a name [X] to an expression of the
    form [epsilon P] that appears in hypothesis [H]. *)

Ltac epsilon_name_core X :=
  epsilon_find ltac:(fun P => sets X: (epsilon P)).

Ltac epsilon_name_in_core X H :=
  epsilon_find_in H ltac:(fun P => sets X: (epsilon P)).

Tactic Notation "epsilon_name" ident(X) :=
  epsilon_name_core X.

Tactic Notation "epsilon_name" ident(X) "in" hyp(H)  :=
  epsilon_name_in_core X H.


(* ---------------------------------------------------------------------- *)
(** ** Tactics to work with [epsilon] *)

(** [epsilon X] locates an expression of the form [epsilon P] in the goal,
    names [X] this expression (like [epsilon_name X]), then produces
    a subgoal [exists x, P x], and leaves at the head of the main goal
    an hypothesis [P X].

    [epsilon X in H] is similar, but looks for [epsilon P] only in
    hypothesis [H]. *)

Lemma pred_epsilon' : forall A (P:A->Prop) (IA:Inhab A),
  (exists x, P x) ->
  P (epsilon P).
Proof using. intros. applys* pred_epsilon. Qed.

Ltac epsilon_cont X P :=
  let I := fresh "H" X in
  lets I: (>> (@pred_epsilon' _ P) __ __);
    [ | sets X: (epsilon P); revert I ].

Ltac epsilon_core X :=
  epsilon_find ltac:(fun P => epsilon_cont X P).

Ltac epsilon_in_core X H :=
  epsilon_find_in H ltac:(fun P => epsilon_cont X P).

Tactic Notation "epsilon" ident(X) :=
  epsilon_core X.
Tactic Notation "epsilon" ident(X) "in" hyp(H) :=
  epsilon_in_core X H.

Tactic Notation "epsilon" "~" ident(X) :=
  epsilon X; auto_tilde.
Tactic Notation "epsilon" "~" ident(X) "in" hyp(H) :=
  epsilon X in H; auto_tilde.

Tactic Notation "epsilon" "*" ident(X) :=
  epsilon X; auto_star.
Tactic Notation "epsilon" "*" ident(X) "in" hyp(H) :=
  epsilon X in H; auto_star.


(* ********************************************************************** *)
(** * Construction of a function from a relation, using [epsilon] *)

(* Given a relation [R] of type [A->B->Prop], [rel_to_fun R] returns a
   function [f] of type [A->B] that satisfies the relation [R], i.e.
   such that [R x (f x)] forall [x] that has an image by [R]. *)

Definition rel_to_fun A `{IB:Inhab B} (R:A->B->Prop) : A -> B :=
  fun (a:A) => epsilon (fun b => R a b).

Section Rel_to_fun.
Context (A B : Type) {IB:Inhab B}.
Implicit Types R : A -> B -> Prop.

(* Every [a] in the domain of [R] is related by [R] with [rel_to_fun a]. *)

Lemma rel_rel_to_fun_of_exists : forall R a,
  (exists b, R a b) ->
  R a (rel_to_fun R a).
Proof using IB. introv [x H]. unfold rel_to_fun. epsilon* y. Qed.

Lemma rel_rel_to_fun_of_rel : forall R a b,
  R a b ->
  R a (rel_to_fun R a).
Proof using IB. intros. applys* rel_rel_to_fun_of_exists. Qed.

Lemma rel_rel_to_fun_of_not_forall : forall R a,
  ~ (forall b, ~ R a b) ->
  R a (rel_to_fun R a).
Proof using IB.
  introv. rew_logic. intros [x H]. applys* rel_rel_to_fun_of_exists.
Qed.

Lemma rel_in_fun_rel_to_fun : forall R,
  functional R ->
  rel_in_fun R (rel_to_fun R).
Proof using IB. unfold rel_in_fun, rel_to_fun. introv M H. epsilon* z. Qed.

(** Reformulation of above *)

Lemma rel_to_fun_eq_of_functional : forall x y R,
  functional R ->
  R x y ->
  rel_to_fun R x = y.
Proof using IB. introv M E. applys* rel_in_fun_rel_to_fun. Qed.

End Rel_to_fun.

(* Remark: in the special case where [R] has type [A->A->Prop],
   one may get away without providing a proof of [Inhab A].

  Definition rel_to_fun' A (R : A -> A -> Prop) (a : A) : A :=
    @rel_to_fun A A (Inhab_of_val a) R a.
*)












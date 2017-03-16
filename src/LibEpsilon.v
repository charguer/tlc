(**************************************************************************
* TLC: A library for Coq                                                  *
* Epsilon operator                                                        *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibRelation.
Generalizable Variables A B.


(* ********************************************************************** *)
(** * Definition and specification of Hilbert's epsilon operator *)

(* ---------------------------------------------------------------------- *)
(** ** Construction of epsilon *)

(** [epsilon P] where [P] is a predicate over an inhabited type [A],
    returns a value [x] of type [A] that satisfies [P], if there exists 
    one such value, else it returns an arbitrary value of type [A]. *)

Lemma Inhab_witness : forall `{Inhab A},
  { x : A | True }.
Proof using. intros. destruct H as [H]. apply~ indefinite_description. Qed.

Lemma epsilon_def : forall `{Inhab A} (P : A->Prop),
  { x : A | (exists y, P y) -> P x }.
Proof using.
  intros A I P. destruct (classicT (exists y, P y)) as [H|H].
    apply indefinite_description. destruct H. exists~ x.
    destruct (@Inhab_witness _ I) as [x _].
     exists x. auto_false~.
Qed.

Definition epsilon `{Inhab A} (P : A->Prop) : A := 
  sig_val (epsilon_def P).


(* ---------------------------------------------------------------------- *)
(** ** Specification of epsilon *)

Lemma epsilon_spec_exists : forall `{Inhab A} (P : A->Prop),
  (exists x, P x) -> 
  P (epsilon P).
Proof using. intros. apply~ (sig_proof (epsilon_def P)). Qed.

Lemma epsilon_inv_exists : forall `{Inhab A} (P Q : A->Prop),
  (exists x, P x) -> 
  (forall x, P x -> Q x) -> Q (epsilon P).
Proof using. introv E M. apply M. apply~ epsilon_spec_exists. Qed.

Lemma epsilon_spec : forall `{Inhab A} (P : A->Prop) x,
  P x -> 
  P (epsilon P).
Proof using. intros. apply* (epsilon_spec_exists). Qed.

Lemma epsilon_inv : forall `{Inhab A} (P Q : A->Prop) x,
  P x -> 
  (forall x, P x -> Q x) -> 
  Q (epsilon P).
Proof using. introv Px W. apply W. apply* epsilon_spec_exists. Qed.

Lemma epsilon_eq : forall A {I:Inhab A} (P P':A->Prop),
  (forall x, P x <-> P' x) ->
  epsilon P = epsilon P'.
Proof using. introv H. fequals. extens*. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Tactics [sets_epsilon] *)

(** [sets_epsilon as X]
    [sets_epsilon in H as X]
      
    assigns a name [X] to an expression of the form [epsilon E]. *)

Lemma epsilon_spec' : forall A (P:A->Prop) (x:A) (H:P x) {IA:Inhab A}, 
  P (epsilon P).
Proof using. intros. applys* epsilon_spec. Qed.

Lemma epsilon_spec_exists' : forall A (P : A->Prop) {IA:Inhab A},
  (exists x, P x) -> 
  P (epsilon P).
Proof using. intros. applys* epsilon_spec_exists. Qed.

Ltac find_epsilon cont :=
  match goal with
  | |- context [epsilon ?E] => cont E
  | H: context [epsilon ?E] |- _ => cont E
  end.

Ltac find_epsilon_in H cont :=
  match type of H with context [epsilon ?E] => cont E end.

Tactic Notation "sets_epsilon" "as" ident(X) :=
  find_epsilon ltac:(fun E => sets X: (epsilon E)).

Tactic Notation "sets_epsilon" "in" hyp(H) "as" ident(X) :=
  find_epsilon_in H ltac:(fun E => sets X: (epsilon E)).


(* ---------------------------------------------------------------------- *)
(** ** Tactics to work with [epsilon] *)

(* LATER: produce [I] in the goal *)

(** [spec_epsilon as X I]
      => finds an expression of the form [epsilon P] in the goal,
         names [X] this expression, and adds an hypothesis [I]
         of type [P X]. It produces the subgoal [exists a, P a].

    [spec_epsilon W as X I]
      => same, but [W] is a witness, so the subgoal is only [P W].
      => also works if [W] is a proof of [P a] for some [a].

    [spec_epsilon as X] 
      => same, with [I] automatically generated, of the form [HX].

    [spec_epsilon in H as X I] and variants 
      => same, but looks for [epsilon E] in hypothesis [H]. *)

Ltac spec_epsilon_post E X W I :=
   first [ lets I: (>> (@epsilon_spec' _ E W) __ __)
         | lets I: (>> (@epsilon_spec' _ E _ W) __)  ];
   [ | sets X: (epsilon E) ].

Ltac spec_epsilon_exists_post E X I :=
   lets I: (>> (@epsilon_spec_exists' _ E) __ __); [ | sets X: (epsilon E) ].

Tactic Notation "spec_epsilon" constr(W) "as" ident(X) simple_intropattern(I) :=
  find_epsilon ltac:(fun E => spec_epsilon_post E X W I).

Tactic Notation "spec_epsilon" constr(W) "in" hyp(H) "as" ident(X) simple_intropattern(I) :=
  find_epsilon_in H ltac:(fun E => spec_epsilon_post E X W I).

(* LATER: missing some variants *)

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
Proof using IB. introv [x H]. unfold rel_to_fun. applys* epsilon_spec. Qed.

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
Proof using IB.
  unfold rel_in_fun, rel_to_fun. introv M H. spec_epsilon~ y as z I. applys* M.
Qed.
  
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












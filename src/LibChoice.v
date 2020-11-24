(**************************************************************************
* TLC: A library for Coq                                                  *
* Proof of the axioms of choice                                           *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibEpsilon LibRelation.
Generalizable Variables A B.

(** This files includes several versions of the axiom of choice.
    This "axiom" is actually proved in terms of indefinite description.
    Remark: the choice results contained in this file are not very
    useful in practice since it is usually more convenient to use
    the epsilon operator directly. *)


(* ********************************************************************** *)
(** * Functional choice *)

(* ---------------------------------------------------------------------- *)
(** ** Functional choice *)

(** This result can be used to build a function from a relation that maps
    every input to at least one output. *)

Lemma functional_choice : forall A B (R:A->B->Prop),
  (forall x, exists y, R x y) ->
  (exists f, forall x, R x (f x)).
Proof using.
  intros. exists (fun x => sig_val (indefinite_description (H x))).
  intro x. apply (sig_proof (indefinite_description (H x))).
Qed.
(* --LATER: the premise is called [defined] in LibRelation *)
(* --LATER: functionality -> definedness? *)


(* ---------------------------------------------------------------------- *)
(** ** Dependent functional choice *)

(** It is a generalization of functional choice to dependent functions. *)

Scheme and_indd := Induction for and Sort Prop.
Scheme eq_indd := Induction for eq Sort Prop.

Lemma dependent_functional_choice :
  forall A (B:A->Type) (R:forall x, B x -> Prop),
  (forall x, exists y, R x y) ->
  (exists f, forall x, R x (f x)).
Proof using.
  introv H.
  pose (B' := { x:A & B x }).
  pose (R' := fun (x:A) (y:B') => projT1 y = x /\ R (projT1 y) (projT2 y)).
  destruct (functional_choice R') as (f,Hf).
    intros x. destruct (H x) as (y,Hy).
     exists (existT (fun x => B x) x y). split~.
  sets proj1_transparent: (fun P Q (p:P/\Q) => let (a,b) := p in a).
  exists (fun x => eq_rect _ _ (projT2 (f x)) _ (proj1_transparent _ _ (Hf x))).
  intros x. destruct (Hf x) as (Heq,HR) using and_indd.
  destruct (f x). simpls. destruct Heq using eq_indd. apply HR.
Qed.

Arguments dependent_functional_choice [A] [B].


(* ---------------------------------------------------------------------- *)
(** ** Guarded functional choice *)

(** Similar to functional choice, except that it targets partial functions *)

Lemma guarded_functional_choice : forall A `{Inhab B} (P : A->Prop) (R : A->B->Prop),
  (forall x, P x -> exists y, R x y) ->
  (exists f, forall x, P x -> R x (f x)).
Proof using.
  intros. apply (functional_choice (fun x y => P x -> R x y)).
  intros. applys* indep_general_premises.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Omniscient functional choice *)

(** Similar to functional choice except that the proof of functionality
    of the relation is given after the fact, for each argument. *)

Lemma omniscient_functional_choice : forall A `{Inhab B} (R : A->B->Prop),
  exists f, forall x, (exists y, R x y) -> R x (f x).
Proof using. intros. apply~ guarded_functional_choice. Qed.


(* ********************************************************************** *)
(** * Functional unique choice *)

(** This section provides a similar set of results excepts that it is
    specialized for the case where each argument has a unique image. *)

(* ---------------------------------------------------------------------- *)
(** ** Functional unique choice *)

Lemma functional_unique_choice : forall A B (R:A->B->Prop),
  (forall x , exists! y, R x y) ->
  (exists! f, forall x, R x (f x)).
Proof using.
  intros. destruct (functional_choice R) as [f Hf].
  intros. apply (ex_of_ex_unique (H x)).
  exists f. split. auto.
   intros g Hg. apply fun_ext_1. intros y.
   apply~ (at_most_one_of_ex_unique (H y)).
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Dependent functional unique choice *)

Theorem dependent_functional_unique_choice :
  forall (A:Type) (B:A->Type) (R:forall (x:A), B x -> Prop),
  (forall (x:A), exists! y : B x, R x y) ->
  (exists! f : (forall (x:A), B x), forall (x:A), R x (f x)).
Proof using.
  intros. destruct (dependent_functional_choice R) as [f Hf].
  intros. apply (ex_of_ex_unique (H x)).
  exists f. split. auto.
   intros g Hg. extens. intros y.
   apply~ (at_most_one_of_ex_unique (H y)).
 Qed.

Arguments dependent_functional_unique_choice [A] [B].


(* ---------------------------------------------------------------------- *)
(** ** Guarded functional unique choice *)

Lemma guarded_functional_unique_choice :
  forall A `{Inhab B} (P : A->Prop) (R : A->B->Prop),
  (forall x, P x -> exists! y, R x y) ->
  (exists f, forall x, P x -> R x (f x)).
Proof using.
  introv I M. apply (functional_choice (fun x y => P x -> R x y)).
  intros. apply* indep_general_premises.
  introv H. destruct* (M _ H) as (y&Hy&_).
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Omniscient functional unique choice *)

Lemma omniscient_functional_unique_choice :
  forall A `{Inhab B} (R : A->B->Prop),
  exists f, forall x, (exists! y, R x y) -> R x (f x).
Proof using.
  intros. destruct (omniscient_functional_choice R) as [f F].
  exists f. introv (y&Hy&Uy). autos*.
Qed.


(* ********************************************************************** *)
(** * Relational choice *)

(** Relational choice can be used to extract from a relation a subrelation
    that describes a function, by mapping every argument to a unique image. *)

(* ---------------------------------------------------------------------- *)
(** ** Relational choice *)

Lemma rel_choice : forall A B (R:A->B->Prop),
  (forall x, exists y, R x y) ->
  (exists R', rel_incl R' R
           /\ forall x, exists! y, R' x y).
Proof using.
  introv H. destruct~ (functional_choice R) as [f Hf].
  exists (fun x y => f x = y). split.
    introv E. simpls. subst~.
    intros x. exists~ (f x).
Qed.

(* --TODO: Dependent relational choice, is it meaningful?, useful? *)


(* ---------------------------------------------------------------------- *)
(** ** Guarded relational choice *)

Lemma guarded_rel_choice : forall A B (P : A->Prop) (R : A->B->Prop),
  (forall x, P x -> exists y, R x y) ->
  (exists R', rel_incl R' R
           /\ forall x, P x -> exists! y, R' x y).
Proof using.
  intros. destruct (rel_choice (fun (x:sig P) (y:B) => R (sig_val x) y))
   as (R',(HR'R,M)).
    intros (x,HPx). destruct (H _ HPx) as (y,HRxy). exists~ y.
  set (R'' := fun (x:A) (y:B) => exists (H : P x), R' (exist P x H) y).
  exists R''. split.
    intros x y (HPx,HR'xy). apply (HR'R _ _ HR'xy).
    intros x HPx. destruct (M (exist P x HPx)) as (y,(HR'xy,Uniq)).
     exists y. split.
       exists~ HPx.
       intros y' (H'Px,HR'xy'). apply Uniq.
        rewrite~ (proof_irrelevance HPx H'Px).
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Omniscient relation choice *)

Lemma omniscient_rel_choice : forall A B (R : A->B->Prop),
  exists R', rel_incl R' R
          /\ forall x, (exists y, R x y) -> (exists! y, R' x y).
Proof using. intros. apply~ guarded_rel_choice. Qed.






(**************************************************************************
* TLC: A library for Coq                                                  *
* Core logical definitions (all imported from the Prelude)                *
**************************************************************************)

Set Implicit Arguments.


(* ********************************************************************** *)
(** * Basic logical connectives *)

(* ---------------------------------------------------------------------- *)
(** ** Definition of [True] *)

(** From Prelude:

    Inductive True : Prop :=
      | I : True.

    Hint Constructors True : core.

  Remark: [constructor] should be renamed to [True_intro].
  Single-letter variable names should be reserved to the user.

*)

(* ---------------------------------------------------------------------- *)
(** ** Definition of [False] *)

(** From Prelude:

    Inductive False : Prop := .

*)


(* ---------------------------------------------------------------------- *)
(** ** Definition of [not] *)

(** From Prelude:

  Definition not (P : Prop) := P -> False.

  Notation "~ x" := (not x) : type_scope.

  Hint Unfold not : core.

*)


(* ---------------------------------------------------------------------- *)
(** ** Definition of [and] *)

(** From Prelude:

    Inductive and (P Q : Prop) : Prop :=
      | conj : P -> Q -> and P Q.

    Notation "P /\ Q" := (and P Q) : type_scope.

    Hint Constructors and : core.

    Lemma proj1 : forall (P Q : Prop), P /\ Q -> P.
    Proof using. autos*. Qed.

    Lemma proj2 : forall (P Q : Prop), P /\ Q -> Q.
    Proof using. autos*. Qed.

  Remark: to follow conventions, [conj] should be renamed to [and_intro].

*)


(* ---------------------------------------------------------------------- *)
(** ** Definition of [or] *)

(** From Prelude:

    Inductive or (P Q : Prop) : Prop :=
      | or_introl : P -> or P Q
      | or_intror : Q -> or P Q.

    Notation "A \/ B" := (or A B) : type_scope.

    Hint Constructors or : core.

  Remark: to follow conventions, constructors should be [or_l] and [or_r].

*)

(* ---------------------------------------------------------------------- *)
(** ** Definition of [iff] *)

(** From Prelude:

      Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

      Notation "P <-> Q" := (iff P Q) : type_scope.

      Hint Unfold iff.

*)


(* ---------------------------------------------------------------------- *)
(** ** Definition of [eq] *)

(** From Prelude:

      Inductive eq (A:Type) (x:A) : A -> Prop :=
        | eq_refl : eq x y.

      Notation "x = y :> A" := (@eq A x y) : type_scope.
      Notation "x = y" := (eq x y) : type_scope.
      Notation "x <> y :> A" := (~ @eq A x y) : type_scope.
      Notation "x <> y" := (~ eq x y) : type_scope.

      Arguments eq_ind [A].
      Arguments eq_rec [A].
      Arguments eq_rect [A].

      Hint Constructors eq : core.

  Remark : to follow conventions, constructors should be named [eq_intro],
  or [refl_eq].
*)


(* ---------------------------------------------------------------------- *)
(** ** Definition of [exists x, P] *)

(** From Prelude:

    Inductive ex (A : Type) (P : A->Prop) : Prop :=
      | ex_intro : forall x, P x -> ex P.

    Notation "'exists' x , p" := (ex (fun x => p))
      (at level 200, x ident, right associativity) : type_scope.
    Notation "'exists' x : t , p" := (ex (fun x:t => p))
      (at level 200, x ident, right associativity,
        format "'[' 'exists'  '/  ' x  :  t ,  '/  ' p ']'")
      : type_scope.

    Hint Constructors ex : core.

*)


(* ---------------------------------------------------------------------- *)
(** ** Definition of [forall x, P] and [P -> Q] *)

(** [forall] and [->] are builtin in the logic.
    [P -> Q] is short for [forall (_:P), Q]. *)

(** From Prelude:

    Definition all (A : Type) (P : A->Prop) := forall (x:A), P x.

*)


(* ---------------------------------------------------------------------- *)
(** ** Definition of [{x | P}] (subset type) *)

(** From Prelude:

    Inductive sig (A : Type) (P : A->Prop) : Type :=
      | exist : forall x, P x -> sig P.

    Notation "{ x | P }" := (sig (fun x => P)) : type_scope.
    Notation "{ x : A | P }" := (sig (fun x:A => P)) : type_scope.
    Add Printing Let sig.

  Remark : to follow conventions, constructor should be named [sig_intro].

*)


(* ---------------------------------------------------------------------- *)
(** ** Definition of [{x & P}] (subset type in Type) *)

(** From Prelude:

    Inductive sigT (A : Type) (P : A -> Type) : Type :=
      | existT : forall x, P x -> sigT P.

    Notation "{ x & P }" := (sigT (fun x:A => P)) : type_scope.
    Notation "{ x : A & P }" := (sigT (fun x:A => P)) : type_scope.
    Add Printing Let sigT.

  Remark : to follow conventions, constructor should be named [sigT_intro].

*)



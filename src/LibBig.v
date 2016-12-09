(**************************************************************************
* TLC: A library for Coq                                                  *
* Shared definitions for containers                                       *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibReflect
  LibRelation LibOperation LibInt LibStruct LibBag.
Generalizable Variables A B K T F.

(* ********************************************************************** *)
(** * Operators *)

(* ---------------------------------------------------------------------- *)
(** ** Definitions *)

Class BigSumMonoid K := { bigSumMonoid : monoid_def K }.

Definition bigsum `{BagFold K F T} `{BigSumMonoid K} (f: F) (E: T) :=
  fold bigSumMonoid f E.

Notation "'\bigsum_{' i '\in' E } B" := (bigsum (fun i => B) E)
  (at level 69, i ident, format "'\bigsum_{' i  '\in'  E }  B").

Global Instance BigSumMonoidZ : BigSumMonoid Z.
Proof. constructor. apply (monoid_ Zplus 0). Qed.

Require Import LibSet.
Goal forall (E: set int), \bigsum_{ i \in E } i = 0.
Abort.

(* Lemma bigsum_split : *)
(*   forall `{BagUnion T} `{BagFold K F T} `{BagDisjoint T} (E F : T), *)
(*   E \# F -> *)
(*   bigsum f (E \u F) =  *)
(* TODO: add corresponding instances about fold *)


Require Import LibRange.

Goal forall (a b: int), \bigsum_{ i \in \set[a, b) } i = 0.
Abort.

Notation "'\bigsum_{' i '\in' [ a , b ) } B" := (bigsum (fun i => B) \set[a, b))
  (at level 69, i ident, format "'\bigsum_{' i  '\in'  [ a ,  b ) }  B").
Notation "'\bigsum_{' i '\in' [ a , b ] } B" := (bigsum (fun i => B) \set[a, b])
  (at level 69, i ident, format "'\bigsum_{' i  '\in'  [ a ,  b ] }  B").
Notation "'\bigsum_{' i '\in' ( a , b ) } B" := (bigsum (fun i => B) \set(a, b))
  (at level 69, i ident, format "'\bigsum_{' i  '\in'  ( a ,  b ) }  B").
Notation "'\bigsum_{' i '\in' ( a , b ] } B" := (bigsum (fun i => B) \set(a, b])
  (at level 69, i ident, format "'\bigsum_{' i  '\in'  ( a ,  b ] }  B").

Goal forall (a b: int), \bigsum_{ i \in \set[a, b) } i = 0.
Abort.
Goal forall (a b: int), \bigsum_{ i \in [a, b) } i = 0.
Abort.

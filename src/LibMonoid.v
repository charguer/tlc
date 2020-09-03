(** DISCLAIMER: the current presentation of monoids uses typeclasses,
    but in fact it's not obvious that typeclasses are needed/useful here.
    Indeed, there is no overloading involved.
    Thus, the interface might change in the near future. *)


(**************************************************************************
* TLC: A library for Coq                                                  *
* Mathematical structures                                                 *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic LibOperation.
Generalizable Variables A B.


(* ********************************************************************** *)
(** * Monoids *)

(* --------------------------------------------------------------------- *)
(** * Structures *)

(** Monoid structure: binary operator and neutral element *)

Record monoid_op (A:Type) : Type := monoid_make {
   monoid_oper : A -> A -> A;
   monoid_neutral : A }.

(** Monoid properties
    Note that field names are suffixed by [_prop] because the corresponding
    properties are also available through typeclass instances. *)
(* -- LATER: factorize [let (o,n) := m] for the record definition *)

Class Monoid A (m:monoid_op A) : Prop := Monoid_make {
   monoid_assoc_prop : let (o,n) := m in assoc o;
   monoid_neutral_l_prop : let (o,n) := m in neutral_l o n;
   monoid_neutral_r_prop : let (o,n) := m in neutral_r o n }.

(** Commutative monoid *)

Class Comm_monoid A (m:monoid_op A) : Prop := Comm_monoid_make {
   comm_monoid_monoid : Monoid m;
   comm_monoid_comm : let (o,n) := m in comm o }.


(* --------------------------------------------------------------------- *)
(** * Examples *)

(** Example:

  Instance monoid_plus_zero:
    Monoid (monoid_make plus 0).
  Proof using.
    constructor; repeat intro; lia.
  Qed.

*)

(* --------------------------------------------------------------------- *)
(** * Properties *)

Section MonoidProp.
Context {A:Type}.

Class Monoid_assoc {m:monoid_op A} := {
  monoid_assoc : assoc (monoid_oper m) }.

Class Monoid_neutral_l {m:monoid_op A} := {
  monoid_neutral_l : neutral_l (monoid_oper m) (monoid_neutral m) }.

Class Monoid_neutral_r {m:monoid_op A} := {
  monoid_neutral_r : neutral_r (monoid_oper m) (monoid_neutral m) }.

Class Monoid_comm {m:monoid_op A} := {
  monoid_comm : comm (monoid_oper m) }.

End MonoidProp.


(* --------------------------------------------------------------------- *)
(** * Derived Properties *)

Section MonoidInst.
Variables (A:Type).
Implicit Types m : monoid_op A.

Global Instance Monoid_assoc_of_Monoid : forall m (M:Monoid m),
  Monoid_assoc (m:=m).
Proof using.
  introv M. constructor. destruct M as [U ? ?]. destruct m. simpl. apply U.
Qed.

Global Instance Monoid_neutral_l_of_Monoid : forall m (M:Monoid m),
  Monoid_neutral_l (m:=m).
Proof using.
  introv M. constructor. destruct M as [? U ?]. destruct m. simpl. apply U.
Qed.

Global Instance Monoid_neutral_r_of_Monoid : forall m (M:Monoid m),
  Monoid_neutral_r (m:=m).
Proof using.
  introv M. constructor. destruct M as [? ? U]. destruct m. simpl. apply U.
Qed.

Global Instance Monoid_of_Comm_monoid : forall m (M:Comm_monoid m),
  Monoid m.
Proof using.
  introv M. destruct M as [U ?]. destruct m. simpl. apply U.
Qed.

Global Instance Monoid_comm_of_Comm_Monoid : forall m (M:Comm_monoid m),
  Monoid_comm (m:=m).
Proof using.
  introv M. constructor. destruct M as [? U]. destruct m. simpl. apply U.
Qed.

End MonoidInst.



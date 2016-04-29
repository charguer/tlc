(**************************************************************************
* TLC: A library for Coq                                                  *
* Mathematical structures                                                 *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibOperation Omega.
Generalizable Variables A B.

(* ********************************************************************** *)
(** * Monoids *)

(* --------------------------------------------------------------------- *)
(** * Structures *)

Record monoid_def (A:Type) : Type := monoid_ {
   monoid_oper : oper2 A;
   monoid_neutral : A }.

Class Monoid (A:Type) (m:monoid_def A) : Prop := {
   monoid_assoc_prop : let (o,n) := m in assoc o;
   monoid_neutral_l_prop : let (o,n) := m in neutral_l o n;
   monoid_neutral_r_prop : let (o,n) := m in neutral_r o n }.

Class Monoid_commutative (A:Type) (m:monoid_def A) : Prop := {
   monoid_commutative_monoid : Monoid m;
   monoid_commutative_comm : let (o,n) := m in comm o }.


(* --------------------------------------------------------------------- *)
(** * Properties *)

Section MonoidProp.
Context {A:Type} {m:monoid_def A}.

Class Monoid_assoc := {
  monoid_assoc : assoc (monoid_oper m) }.

Class Monoid_neutral_l := {
  monoid_neutral_l : neutral_l (monoid_oper m) (monoid_neutral m) }.

Class Monoid_neutral_r := {
  monoid_neutral_r : neutral_r (monoid_oper m) (monoid_neutral m) }.

Class Monoid_comm := {
  monoid_comm : comm (monoid_oper m) }.

End MonoidProp.


(* --------------------------------------------------------------------- *)
(** * Derived Properties *)

Section MonoidInst.
(* TODO: use M as explicit hypothesis *)
Context {A:Type} {m:monoid_def A}.

Global Instance Monoid_Monoid_assoc :
  forall {M:Monoid m},
  Monoid_assoc (m:=m).
Proof using.
  introv M. constructor. destruct M as [U ? ?]. destruct m. simpl. apply U.
Qed.

Global Instance Monoid_Monoid_neutral_l :
  forall {M:Monoid m},
  Monoid_neutral_l (m:=m).
Proof using.
  introv M. constructor. destruct M as [? U ?]. destruct m. simpl. apply U.
Qed.

Global Instance Monoid_Monoid_neutral_r :
  forall {M:Monoid m},
  Monoid_neutral_r (m:=m).
Proof using.
  introv M. constructor. destruct M as [? ? U]. destruct m. simpl. apply U.
Qed.

Global Instance Monoid_commutative_Monoid :
  forall {M:Monoid_commutative m},
  Monoid m.
Proof using.
  introv M. destruct M as [U ?]. destruct m. simpl. apply U.
Qed.

Global Instance Monoid_commutative_Monoid_comm :
  forall {M:Monoid_commutative m},
  Monoid_comm (m:=m).
Proof using.
  introv M. constructor. destruct M as [? U]. destruct m. simpl. apply U.
Qed.

End MonoidInst.


(* --------------------------------------------------------------------- *)
(** * Examples *)

Instance monoid_plus_zero:
  Monoid (monoid_ plus 0).
Proof using.
  constructor; repeat intro; omega.
Qed.


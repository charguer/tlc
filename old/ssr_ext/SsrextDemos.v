(**************************************************************************
* Demos                                                                   *
* Arthur Chargueraud                                                      *
* Distributed under the terms of the Cecil-B license                      *
***************************************************************************)

Set Implicit Arguments.
Require Import ssreflect.
Require Import Ssrext.


(* ********************************************************************** *)
(** ** Duplication tactic used in demos *)

(** [dup N] produces [N] copies of the current goal. It is useful
    for building examples on which to illustrate behaviour of tactics.
    [dup] is short for [dup 2]. *)

Lemma dup_lemma : forall P, P -> P -> P.
Proof using. auto. Qed.

Ltac dup_tactic N :=
  match (*nat_from_number*) N with
  | 0 => idtac
  | S 0 => idtac
  | S ?N' => apply dup_lemma; [ | dup_tactic N' ]
  end.

Tactic Notation "dup" constr(N) := 
  dup_tactic N.
Tactic Notation "dup" := 
  dup 2.


(* ********************************************************************** *)
(** ** Introv tactic used in demos ==> to be replaced by "move" *)

Ltac introv_arg H :=
  hnf; match goal with
  | |- ?P -> ?Q => intros H
  | |- forall _, _ => intro; introv_arg H
  end.

Tactic Notation "introv" simple_intropattern(I1) :=
  introv_arg I1.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) :=
  introv I1; introv I2.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) :=
  introv I1; introv I2 I3.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) :=
  introv I1; introv I2 I3 I4.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  introv I1; introv I2 I3 I4 I5.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  introv I1; introv I2 I3 I4 I5 I6.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  introv I1; introv I2 I3 I4 I5 I6 I7.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "introv" simple_intropattern(I1) simple_intropattern(I2) 
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  introv I1; introv I2 I3 I4 I5 I6 I7 I8 I9 I10.



(* ********************************************************************** *)
(** ** Definitions used in demos *)

Variables H1 H2 H3 H4 H5 H6 : Prop.
Variables P1 P2 P3 : nat -> Prop.


(* ********************************************************************** *)
(** ** Assertions, cuts, contradiction *)

Lemma demo_false_1 : 
  forall (n:nat), (forall m, m = n -> False) -> H1.
Proof using.
  intros n P. dup 4.
  (* [false_goal] replaces the current goal by [False] *)
  false. eapply P. reflexivity.
  (* [false E] proves the goal if [E] has type [False] *)
  false (P n (refl_equal n)).
  (* [false E] is in fact the same as [false; apply E] *)
  false P. reflexivity.
  (* [false] also tries and call [congruence] *)
  lets (P n). intros. false.
Qed.

Lemma demo_false_2 : 
  0 = 1 -> 1 = 2.
Proof using.
  intros. dup 3.
  (* [contradiction] does not cover [discriminate] *)
  try contradiction. admit. 
  discriminate.
  (* while [false] covers [contradiction] and [discriminate] *)
  false.
Qed.

Lemma demo_false_3 : 
  (forall b, b = false) -> False.
Proof using.
  intros H. dup.
  (* [false E] is able to use [forwards E] to exhibit 
     a contradiction. *)
  false (>> H true).
  (* syntax [false E1 .. EN] is also available *)
  false H true.
Qed.

Lemma demo_tryfalse : 
  forall n, S n = 1 -> n = 0.
Proof using.
  intros. dup 2.
  (* often in a case analysis, several subcases are absurd. example: *)
  destruct n. auto. false.
  (* [tryfalse] removes all the subcases solved by [false] *)
  destruct n; tryfalse. auto.
Qed.



(* ********************************************************************** *)
(** * Inversions *)

Inductive even_shift : nat -> nat -> Prop :=
  | even_0 : even_shift 0 2
  | even_SS : forall n m, even_shift n m -> 
              even_shift (S (S n)) (S (S m)).

Lemma demo_invert : 
  even_shift 4 8 -> False.
Proof using.
  intros P. dup 5.
  (* [inversion] generates a lot of ugly stuff *)
  inversion P. inversion H7. inversion H10.
  (* [invert] is same as [inversion H; clear H] except that it
     generalizes the generated hypotheses so that they can 
     be named manually using intros or introv *)
  invert P. introv P' EQ1 EQ2. admit.
  (* [inverts] does the same as [inversion; clear], then it 
     substitutes all the generated equalities (and only
     these fresh equalities, not the older ones) *)
  inverts P. intros. inverts H7. intros. inverts H8. admit.
  (* one may add the keyword [keep] in order to keep the
     inverted hypothesis *)
  invert keep P. intros. admit.
Qed.
   
Inductive Behave : Type := 
  | Behave_intro : 
      forall (A:Type) (F:A->nat) (P:A->Prop), Behave.

Inductive behave : nat -> Behave -> Prop :=
  | behave_intro : forall (A:Type) (F:A->nat) (P:A->Prop) V,
      P V -> behave (F V) (@Behave_intro A F P).

Lemma demo_dependent_invert : 
  behave 4 (Behave_intro (fun x:nat => x) (fun x:nat => x <> 3))
  -> False.
Proof using.
  intros H. dup 2.
  (* [inversion] can generate some dependently-typed equalities *)
  inversion H. (* look at H9 and H10 *) admit.
  (* [inverts] carries out all the substitution properly *) 
  inverts H. admit.
Qed.



(* ********************************************************************** *)
(** ** Advanced instantiation *)

(* Note: the use of "instantiation modes" is described in the overview file
   and described in full details in the source file LibTactics.v *)

Lemma demo_lets_of : forall (x y : nat) (A B : Prop),
  (x > 0) ->
  (x <> y) -> 
  (A <-> B) ->
  (forall n, n > 0 -> forall m, n <> m -> exists k, k <> m) ->
  (forall n : nat, 
   n > 0 ->
   forall P Q : Prop,
   (P <-> Q) ->
   forall m : nat,
   n <> m ->
   forall K : nat -> Prop,
   K n -> 
   forall p,
   K (m+p) -> 
   True) ->
  True.
Proof using.
  introv Pos Neq Iff L M.
  (* [lets] is used to instantiate a lemma [M] on arguments *)

  lets M Iff. eauto. intros _.
  lets (>> M Neq). eauto. eauto. intros _.
  lets (>> M __ y). eauto. eauto. intros _.
  lets (>> M x __ B). eauto. instantiate (1:=A). intros _.
  lets (>> M __ y Neq). eauto. eauto. intros _.
  (* The syntax [>>] is not required for less than 5 arguments. *)
  lets M Pos A B Neq. eauto. intros _.
  (* A triple underscore indicates to instantiate all remaining *)
  lets (>> L Pos ___). eauto. move=> [k K]. clears k.
  lets (>> L ___). eauto. eauto. intros _.
  (* [forwards I: (>> E E1 .. EN)] is short for
     [lets I: (>> E E1 .. EN ___)] *)
  forwards L. eauto. eauto. intros _.
  forwards L Pos. eauto. intros _.
  forwards (>> L x y). eauto. eauto. intros _.
  forwards (>> L Neq). eauto. intros _.
  auto.
Qed.


Lemma demo_forwards_1 : forall x : nat, x > 1 ->
  (forall z, z > 1 -> exists y, z < 2 /\ z <> y) -> 
  True.
Proof using.
  introv Le H. dup 4.
  (* [forwards] is used to instantiate a lemma entirely, generating one
     subgoal for each hypothesis and one existential variable for 
     each universally quantified variable *)
  forwards H. eauto. admit.
  (* an introduction-pattern can be used to decompose the result *)
  forwards H. eauto. (* move [y [R1 R2]] *)  admit.
  (* and [forwards] can also be used without introduction pattern *)
  forwards H. eauto. admit.
  (* [forwards] does nothing on an hypothesis without quantifiers *)
  forwards Le. admit.
Qed.



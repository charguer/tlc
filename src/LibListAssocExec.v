(**************************************************************************
* TLC: A library for Coq                                                  *
* Executable operations for association lists                             *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
From TLC Require Import LibTactics LibReflect.
From TLC Require Export LibListAssoc.


(* ---------------------------------------------------------------------- *)
(* ** Executable [get_opt] *)

Fixpoint get_opt A (beq:A->A->bool) B (a:A) (l:list(A*B)) : option B :=
  match l with
  | nil => None
  | (x,v)::l' => if beq x a
                   then Some v
                   else get_opt beq a l'
  end.

Lemma get_opt_eq : forall A beq B a (l:list(A*B)),
  is_beq beq ->
  get_opt beq a l = LibListAssoc.get_opt a l.
Proof using.
  introv M. induction l as [|(x,v) l']; simpl.
  { rewrite~ get_opt_nil. }
  { rewrite~ get_opt_cons. rewrite M. repeat case_if; auto. }
Qed.

(* ---------------------------------------------------------------------- *)
(* ** Executable [remo] *)

Fixpoint rem A (beq:A->A->bool) B (x:A) (E:list(A*B)) : list(A*B) :=
  match E with
  | nil => nil
  | (y,v)::E' =>
      let E'' := rem beq x E' in
      if beq x y then E'' else (y,v)::E''
  end.

Lemma rem_eq : forall A beq B a (l:list(A*B)),
  is_beq beq ->
  rem beq a l = LibListAssoc.rem a l.
Proof using.
  introv M. induction l as [|(x,v) l']; simpl.
  { rewrite~ rem_nil. }
  { rewrite~ rem_cons. rewrite M. repeat case_if; fequals. }
Qed.


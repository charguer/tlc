From TLC Require Import LibTactics.
From Coq Require Import ZArith.

(**************************************************************************)
(** * Overloading *)

(** Ideally, we'd have ADA/PVS style resolution of overloading,
    directed both by the type of function arguments and the type
    expected by the context, using a two-pass typing algorithm
    (bottom-up, then top-down). For the moment, let me approximate
    this feature by using:
    - typeclass for parsing and resolving overloaded symbols
    - immediate call to "simpl" to remove the typeclass indirection
    - use of printing-only notation for printing the overloaded symbols. *)

Class Plus (A B C:Type) : Type := 
  { plus : A -> B -> C }.

Instance Plus_nat : Plus nat nat nat.
Proof using. constructor. apply Nat.add. Defined.

Instance Plus_Z : Plus Z Z Z.
Proof using. constructor. apply Z.add. Defined.

Class Zero (A:Type) : Type := 
  { zero : A }.

Instance Zero_nat : Zero nat.
Proof using. constructor. apply 0%nat. Defined.

Instance Zero_Z : Zero Z.
Proof using. constructor. apply 0%Z. Defined.


(** The tactic [over] unfolds overloading instances. *)
Ltac over := unfold plus, zero; simpl.

(** To avoid confusion with existing scopes, we temporary use '0 and
    '+ symbols. *)

Declare Scope maths_scope.
Open Scope maths_scope.

Notation "'0" := (@zero _) (at level 0, only parsing) : maths_scope.
Notation "n '+ m" := (@plus _ _ _ _ n m) (at level 40, only parsing) : maths_scope.

Notation "'0" := (0%nat) (at level 0, only printing) : maths_scope.
Notation "'0" := (0%Z) (at level 0, only printing) : maths_scope.

Notation "n '+ m" := (Nat.add n m) (at level 40, only printing) : maths_scope.
Notation "n '+ m" := (Z.add n m) (at level 40, only printing) : maths_scope.

(** Example *)

Lemma test_plus : forall (a b : nat) (c d : Z), 
 c '+ d '+ '0 = Z.of_nat (a '+ b '+ '0).
Proof using.
  over. intros.
Abort.


(**************************************************************************)
(** * Overloading *)
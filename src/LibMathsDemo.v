Set Implicit Arguments.
From TLC Require Import LibTactics LibList.
From Coq Require Import ZArith Even.


Declare Scope maths_scope.
Open Scope maths_scope.


(**************************************************************************)
(** * Properties of operators *)

(** This material from this section is an excerpt from TLC's [LibOperation.v] *)

Section Definitions.
Variables (A : Type).
Implicit Types f g : A -> A -> A.
Implicit Types i : A -> A.


(* ---------------------------------------------------------------------- *)
(** ** Commutativity, associativity *)

(** Commutativity *)

Definition comm f := forall x y,
  f x y = f y x.

(** Associativity *)

Definition assoc f := forall x y z,
  f x (f y z) = f (f x y) z.

(** Combined associativity commutativity *)

Definition comm_assoc f := forall x y z,
  f x (f y z) = f y (f x z).


(* ---------------------------------------------------------------------- *)
(** ** Distributivity *)

(** Distributivity of unary operator *)

Definition distrib i f := forall x y,
  i (f x y) = f (i x) (i y).

(** comm distributivity of unary operator *)

Definition distrib_comm i f := forall x y,
  i (f x y) = f (i y) (i x).

(** Left distributivity *)

Definition distrib_l f g := forall x y z,
  f x (g y z) = g (f x y) (f x z).

(** Right distributivity *)

Definition distrib_r f g := forall x y z,
  f (g y z) x = g (f y x) (f z x).


(* ---------------------------------------------------------------------- *)
(** ** Neutral and absorbant *)

(** Left Neutral *)

Definition neutral_l f e:= forall x,
  f e x = x.

(** Right Neutral *)

Definition neutral_r f e := forall x,
  f x e = x.

(** Left Absorbant *)

Definition absorb_l f a := forall x,
  f a x = a.

(** Right Absorbant *)

Definition absorb_r f a := forall x,
  f x a = a.

End Definitions.


(**************************************************************************)
(** * From maths to Coq *)

(* ---------------------------------------------------------------------- *)
(** Constrained quantification *)

(** "Let [L] be a list of natural numbers" 
    is naturally translated as a quantification over a value of type [list nat]. *)

Definition example_list_nat :=
  forall (L : list nat), True.

(** "Let [L] be a list of even natural numbers"
    is naturally translated as a quantification over a value of type [list nat],
    with an additional constraint on the values stored in the list. *)

Definition example_list_even_nat :=
  forall (L : list nat), LibList.Forall even L -> True.

(** "Let [L] be a list of positive natural numbers"
    if we follow the scheme of the previous example, we get: *)

Definition example_list_pos_nat :=
  forall (L : list nat), LibList.Forall (fun v => v > 0) L -> True.

(** In other words, there is no reason to come up with a new type [natpos]
    for nonnegative numbers, and quantify over [L : list natpos]. *)

(** "Let [L] be a list of natural numbers whose length is between 5 and 7"
    is, again, naturally translated as a quantification over a value of type 
    [list nat], with an additional constraint on the list. *)

Definition example_list_nat_bounded :=
  forall (L : list nat), (5 <= length L <= 7) -> True.

(** "Let [n] be natural number and [L] be a list of length [n]"
    is just a special case of the previous example. *)

Definition example_list_nat_exact :=
  forall (n : nat) (L : list nat), (length L = n) -> True.

(** In other words, there is no reason to come up with a new dependent type
    [list n nat] for lists of [n] values of type [nat]. *)

(** "Let [n] be a list of length [5]" 
    involves an implicit quantification over the type of the list.
    If we are explicit, in type theory, we would write: *)

Definition example_list_poly :=
  forall (A : Type) (L : list A), (length L = 5) -> True.

(** If we want to leave the quantification over the type explicit, we would
    need a mechanism that generalizes "Implicit Types". I would like to write:
[[
  Autoquantify (A : Type).

  Implicit Types (L : list A).

  Definition example_list_poly :=
    forall L, (length L = 5) -> True.
]]
    and obtain the same definition as the explicit one.
*)

(* ---------------------------------------------------------------------- *)
(** Sets *)

(** Assume now an abstract type [set A] for possibly infinite sets. *)

Parameter set : Type -> Type. 
 (* e.g. [A -> Prop] *)
Parameter mem : forall A, A -> set A -> Prop. 
 (* e.g. [fun x E => E x] *)
Parameter finite : forall A, set A -> Prop.
 (* e.g., defined in terms of a list enumeration of the elements *)
Parameter card : forall A, set A -> nat. 
 (* e.g., defined using [epsilon], and returning arbitrary values for nonfinite sets;
   it is not the more general function with meaningful return values for infinite sets *)


(** Let us introduce two notations (not overloaded, for simplicity)
    to help us state lemmas. *)

Notation "x '\in' E" := (mem x E)
  (at level 39) : maths_scope.

Notation "'forall_' x '\in' E ',' P" :=
  (forall x, mem x E -> P)
  (at level 200, x ident) : maths_scope.

(** "Let [E] be a set" (without presuming finiteness)
    should be translated just like lists. *)

Definition example_set_poly :=
  forall (A : Type) (E : set A), True.

(** "Let [E] be a set of cardinality [5]"
    should be translated like lists of bounded length. *)

Definition example_set_card :=
  forall (A : Type) (E : set A), card E = 5 -> True.

(** "Let [E] be a finite set"
    should be translated in a similar way as cardinality constraints. *)

Definition example_set_finite :=
  forall (A : Type) (E : set A), finite E -> True.

(** In other words, there is no need for a special type [fset] for
    finite sets. *)

(** "Let [E] be a set of natural numbers such that, for any element 
    [x] in [E], the number [x] is even." *)

Definition example_set_even :=
  forall (E : set nat), forall_ x \in E, even x -> True.


(**************************************************************************)
(** * Mathematical functions *)

(** "A function [f] from [E] to [F], written [E -> F], maps elements from the set [E] 
    into the set [F]." 
    We can translate this in type theory as follows. *)

Definition function (A B:Type) (E:set A) (F:set B) (f:A->B) : Prop :=
  forall_ x \in E, (f x) \in F.

(** "A function [f] is a binary operation over a set [E] if it maps pairs of
    elements from [E] to elements from the set [E]."  
    We view [f] as a curried function (more idiomatic in type theory),
    and translate the statement as: *)

Definition internal_binop (A:Type) (E:set A) (f:A->A->A) : Prop :=
   forall_ x \in E, forall_ y \in E, (f x y) \in E.


(**************************************************************************)
(** * Algebraic structures *)

(* ---------------------------------------------------------------------- *)
(** Definitions *)

(** "A set S equipped with a binary operation [S x S -> S], and with member
    an identity element is a monoid if it satisfies the two axioms
    (associativity and identity element)."

    Here, the set [S] is of unspecified type, so let us apply the previous
    scheme of assuming an implicit quantification of a type [A] for the elements.

    We could attempt to formalize this directly as a predicate
    [monoid S id op]. But instead of carrying [S], [id] and [op] as three
    separate components everywhere, let us first introduce a type for the 
    set equipped with its identity element and its binary operation. *)

Record monoid_str (A:Type) : Type := monoid_ {
   monoid_set : set A;
   monoid_id : A;
   monoid_op : A -> A -> A; }.

(** Then, let us define the property "is a monoid" for such a structure *)
(* Note: can I factorize [let '(E,id,op) := M in] inside this definition? *)

Record monoid (A:Type) (M:monoid_str A) : Type := monoid_make {
   monoid_op_internal : let (E,id,op) := M in internal_binop E op;
   monoid_assoc_prop : let (E,id,op) := M in assoc op;
   monoid_neutral_l_prop : let (E,id,op) := M in neutral_l op id;
   monoid_neutral_r_prop : let (E,id,op) := M in neutral_r op id }.

(** "A monoid whose operation is commutative is called a commutative monoid".
    We translate that as follows. *)

Record comm_monoid (A:Type) (M:monoid_str A) : Type := comm_monoid_make {
   comm_monoid_monoid : monoid M;
   comm_monoid_comm : let (E,id,op) := M in comm op }.

(** "Let M(op,id) be a commutative monoid. We have [op id id = id]."
    is translated as: *)

Definition example_comm_monoid :=
  forall (A : Type) (M : monoid_str A), comm_monoid M ->
  let (E,id,op) := M in 
  op id id = id.

(** See further on for the version with notation:
   "Let M(+,0) be a commutative monoid. We have ['0 '+ '0 = '0]." *)

Definition example_comm_monoid_notations :=
  forall (A : Type) (M : monoid_str A), comm_monoid M ->
  let (E,id,op) := M in 
  op id id = id.





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
















































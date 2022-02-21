Set Implicit Arguments.
From TLC Require Import LibTactics LibList.
From Coq Require Import ZArith Even.

Declare Scope maths_scope.
Open Scope maths_scope.



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
Parameter set_st : forall A, (A -> Prop) -> set A. 
 (* e.g. identity function *)
Parameter mem : forall A, A -> set A -> Prop. 
 (* e.g. [fun x E => E x] *)
Parameter finite : forall A, set A -> Prop.
 (* e.g., defined in terms of a list enumeration of the elements *)
Parameter card : forall A, set A -> nat. 
 (* e.g., defined using [epsilon], and returning arbitrary values for nonfinite sets;
   it is not the more general function with meaningful return values for infinite sets *)

Parameter mem_set_st_eq : forall A (P:A->Prop) (x:A), 
  (mem x (set_st P)) = (P x).

(** Let us introduce two notations (not overloaded, for simplicity)
    to help us state lemmas. *)

Notation "x '\in' E" := (mem x E)
  (at level 39) : maths_scope.

Notation "'forall_' x '\in' E ',' P" :=
  (forall x, mem x E -> P)
  (at level 200, x ident) : maths_scope.

Notation "'forall_' x y '\in' E ',' P" :=
  (forall x y, mem x E -> P)
  (at level 200, x ident, y ident) : maths_scope.

Notation "'forall_' x y z '\in' E ',' P" :=
  (forall x y z, mem x E -> P)
  (at level 200, x ident, y ident, z ident) : maths_scope.

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
   forall_ x y \in E, (f x y) \in E.

(** Properties of binary operators over sets *)

Definition comm (A:Type) (E:set A) (f:A->A->A) : Prop := 
  forall_ x y \in E, f x y = f y x.

Definition assoc (A:Type) (E:set A) (f:A->A->A) : Prop := 
  forall_ x y z \in E, f x (f y z) = f (f x y) z.

Definition neutral_l (A:Type) (E:set A) (f:A->A->A) (e:A) : Prop :=
  forall_ x \in E, f e x = x.

Definition neutral_r (A:Type) (E:set A) (f:A->A->A) (e:A) : Prop :=
  forall_ x \in E, f x e = x.

Definition neutral_lr (A:Type) (E:set A) (f:A->A->A) (e:A) :=
  neutral_l E f e /\ neutral_r E f e.


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
   monoid_assoc_prop : let (E,id,op) := M in assoc E op;
   monoid_neutral_lr_prop : let (E,id,op) := M in neutral_lr E op id }.

(** "A monoid whose operation is commutative is called a commutative monoid".
    We translate that as follows. *)

Record comm_monoid (A:Type) (M:monoid_str A) : Type := comm_monoid_make {
   comm_monoid_monoid : monoid M;
   comm_monoid_comm : let (E,id,op) := M in comm E op }.

(** "Let M(id,op) be a commutative monoid. We have [op id id = id]."
    is translated as: *)

Definition example_comm_monoid :=
  forall (A : Type) (M : monoid_str A), comm_monoid M ->
  let (E,id,op) := M in 
  op id id = id.

(** See further on for the version with notation:
   "Let M(0,+) be a commutative monoid. We have ['0 '+ '0 = '0]." *)


(* ---------------------------------------------------------------------- *)
(** Properties *)

(** Smart constructor *)

Lemma monoid_of_monoid_destruct : forall (A : Type) (M : monoid_str A),
  monoid M ->
  monoid {| monoid_set := monoid_set M; monoid_id := monoid_id M; monoid_op := monoid_op M |}.
Proof using. intros ? []. auto. Qed.

(** Extract a monoid from a comm_monoid *)

Lemma monoid_of_comm_monoid : forall (A : Type) (M : monoid_str A),
  comm_monoid M ->
  monoid M.
Proof using. introv []. auto. Qed.

Hint Resolve monoid_of_monoid_destruct monoid_of_comm_monoid.

(** Extract properties from a monoid *)

Lemma assoc_of_monoid : forall (A : Type) (E : set A) (op : A->A->A) (id:A),
  monoid (monoid_ E id op) ->
  assoc E op.
Proof using. introv []. auto. Qed.

Lemma neutral_l_of_monoid : forall (A : Type) (E : set A) (op : A->A->A) (id:A),
  monoid (monoid_ E id op) ->
  neutral_l E op id.
Proof using. introv [? ? [HN ?]]. auto. Qed.

Hint Resolve neutral_l_of_monoid.

(* ---------------------------------------------------------------------- *)
(** Monoid over full types *)


(** [Z] is a communative monoid for [0] and [+]. In this monoid, the type [A] of elements
    is [Z], and the set [E] is all of [Z]. This pattern of having a structure
    over a full type is common, so it is worth introducing simplified, derived
    definitions for this case. *)

Record monoidt_str (A:Type) : Type := monoidt_ {
   monoidt_id : A;
   monoidt_op : A -> A -> A; }.

(** A monoid on a full type is a monoid on the set of all elements of that type *)

Definition set_full (A:Type) : set A :=
  set_st (fun (_:A) => True).

Coercion monoidt_of_monoidt (A:Type) (M:monoidt_str A) : monoid_str A :=
  {| monoid_set := set_full A;
     monoid_id := monoidt_id M;
     monoid_op := monoidt_op M |}.

(** Properties for full operators *)

Definition commt (A:Type) (f:A->A->A) : Prop := 
  forall x y, f x y = f y x.

Definition assoct (A:Type) (f:A->A->A) : Prop := 
  forall x y z, f x (f y z) = f (f x y) z.

Definition neutralt_l (A:Type) (f:A->A->A) (e:A) : Prop :=
  forall x, f e x = x.

Definition neutralt_r (A:Type) (f:A->A->A) (e:A) : Prop :=
  forall x, f x e = x.

Definition neutralt_lr (A:Type) (f:A->A->A) (e:A) :=
  neutralt_l f e /\ neutralt_r f e.

(** Smart constructors *)

Lemma monoidt : forall (A:Type) (op : A->A->A) (id:A),
  assoct op ->
  neutralt_lr op id ->
  monoid (monoidt_ id op).
Admitted.

Lemma comm_monoidt : forall (A:Type) (op : A->A->A) (id:A),
  let M := monoidt_ id op in
  monoid M ->
  commt op ->
  comm_monoid M.
Admitted.

(** Demo: [Z] additive monoidt *)

Lemma example_monoidt_Z :
  comm_monoid (monoidt_ 0%Z Z.add).
Proof using.
  apply comm_monoidt.
  { apply monoidt; try split; intros_all; try omega. }
  { intros_all; try omega. }
Qed.

(** Extract properties from a full monoidt *)

Lemma assoc_of_monoidt : forall (A : Type) (op : A->A->A) (id:A),
  monoid (monoidt_ id op) ->
  assoct op.
Proof using.
  introv [? HA ?]. simpls. intros x y z. applys HA. unfold set_full. rewrite* mem_set_st_eq.
Qed.

Lemma neutral_l_of_monoidt : forall (A : Type) (op : A->A->A) (id:A),
  monoid (monoidt_ id op) ->
  neutralt_l op id.
Proof using.
  introv [? ? [HN ?]]. simpls. intros x. applys HN. unfold set_full. rewrite* mem_set_st_eq.
Qed.

(** Demo: associativity [Z] additive monoidt *)

Hint Resolve example_monoidt_Z.

Lemma example_monoidt_Z_assoc : forall x y z,
  Z.add x (Z.add y z) = Z.add (Z.add x y) z.
Proof using.
  intros. rewrite assoc_of_monoidt; eauto.
Qed.


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

(** Instances and printing for monoids *)

Instance Zero_monoid : forall (A:Type) (M:monoid_str A),
  Zero A.
Proof using. constructor. apply (monoid_id M). Defined.

Instance Plus_monoid : forall (A:Type) (M:monoid_str A),
  Plus A A A.
Proof using. constructor. apply (monoid_op M). Defined.

Definition SetZeroPlus_of_monoid (A:Type) (M:monoid_str A) : set A * Zero A * Plus A A A :=
  (monoid_set M, Zero_monoid M, Plus_monoid M).

Definition ZeroPlus_of_monoidt (A:Type) (M:monoidt_str A) : Zero A * Plus A A A :=
  (Zero_monoid M, Plus_monoid M).

Notation "'0" := (monoid_id _) (at level 0, only printing) : maths_scope.
Notation "'0" := (monoidt_id _) (at level 0, only printing) : maths_scope.

Notation "n '+ m" := (monoid_op _ n m) (at level 40, only printing) : maths_scope.
Notation "n '+ m" := (monoidt_op _ n m) (at level 40, only printing) : maths_scope.


(** "Let M(E,+,0) be a commutative monoid. 
    For any [x] in [E], we have ['0 '+ x = x]." *)

Lemma example_comm_monoid_notations :
  forall (A : Type) (M : monoid_str A), comm_monoid M ->
  let '(E,_,_) := SetZeroPlus_of_monoid M in (* declare additive symbols for [M] *)
  forall_ x \in E,  '0 '+ x = x.
Proof using.
  over. introv HM Hx.
 (* prints as [x '+ '0 = x] *)
 (* stands for [monoid_op M x (monoid_id M) = x] *)
  rewrites (>> neutral_l_of_monoid Hx).
  { eauto. } (* monoid_of_comm_monoid *)
  { eauto. } (* solves [x = x]. *)
Qed.

(** Same example with a monoid on a full type *)

Lemma example_comm_monoidt_notations :
  forall (A : Type) (M : monoidt_str A), comm_monoid M ->
  let '(_,_) := ZeroPlus_of_monoidt M in (* declare additive symbols for [M] *)
  forall x,  '0 '+ x = x.
Proof using. 
  over. introv HM. intros x.
 (* prints as [x '+ '0 = x] *)
 (* stands for [monoid_op M x (monoid_id M) = x] *)
  rewrite neutral_l_of_monoidt.
  { eauto. } (* solves [x = x]. *)
  { eauto. } (* monoid_of_comm_monoid *)
Qed.






































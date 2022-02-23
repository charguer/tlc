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
Parameter union : forall A, set A -> set A -> set A.
 (* e.g. [fun x E => E x] *)
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

Notation "E '\u' F" := (union E F)
  (at level 35) : maths_scope.

Notation "'forall_' x '\in' E ',' P" :=
  (forall x, mem x E -> P)
  (at level 200, x ident) : maths_scope.

Notation "'forall_' x y '\in' E ',' P" :=
  (forall x y, mem x E -> mem y E -> P)
  (at level 200, x ident, y ident) : maths_scope.

Notation "'forall_' x y z '\in' E ',' P" :=
  (forall x y z, mem x E -> mem y E -> mem z E -> P)
  (at level 200, x ident, y ident, z ident) : maths_scope.

(** "Let [E] be a set" (without presuming finiteness)
    should be translated just like lists. *)

Definition example_set_poly :=
  forall (A : Type) (E : set A), True.

(** "Let [E], [F], [G] be three sets. Then [E \u (F \u G) = (G \u E) \u F]"
    for translating this statement, we exploit the implicit assumption that
    the sets are homogeneous. *)

Definition example_set_union :=
  forall (A : Type) (E F G : set A), E \u (F \u G) = (G \u E) \u F.

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

(** Assume the notation "forall (x st P), .."  means "forall x, P x -> ..".
    The example above can be written:

[[
  Autoquantify (A : Type).
  Implicit Types (E : set A).
  Definition example_set_finite :=
   forall (E st finite), True.
]]
*)

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
    We view [f] as a curried function (more idiomatic in type theory).
    We write [set_op E f] to means that [f] is an internal operation on [E]. *)

Definition set_op (A:Type) (E:set A) (f:A->A->A) : Prop :=
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
    Consider for example the monoid [2Z], made of even integers; its carrier
    type is [Z], but its elements are only the subset of even integers.

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
   monoid_set_id : let (E,id,op) := M in (id \in E);
   monoid_set_op : let (E,id,op) := M in (set_op E op);
   monoid_assoc : let (E,id,op) := M in (assoc E op);
   monoid_neutral_lr : let (E,id,op) := M in (neutral_lr E op id) }.


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

(** To extract a specific property, e.g. associativity, from a monoid,
    we can use the following lemma. *)

Lemma assoc_of_monoid' : forall (A : Type) (M : monoid_str A),
  monoid M ->
  assoc (monoid_set M) (monoid_op M).
Proof using. intros ? [? ? ?] [? ? ? ?]. auto. Qed.

(** The lemma above works well for forward instantiation, but not for
    backward application. To that end, we introduce another statement
    that applies to any operation, and that triggers the search for
    a monoid associated with that operation. *)

Lemma assoc_of_monoid : forall (A : Type) (E : set A) (op : A->A->A) (id:A),
  monoid (monoid_ E id op) ->
  assoc E op.
Proof using. introv []. auto. Qed.

Lemma neutral_l_of_monoid : forall (A : Type) (E : set A) (op : A->A->A) (id:A),
  monoid (monoid_ E id op) ->
  neutral_l E op id.
Proof using. introv [? ? ? [HN ?]]. auto. Qed.

Hint Resolve neutral_l_of_monoid.

(** A demo of exploiting backward lemmas appear further on. *)

(** Note that the forward application lemmas are easily derivable from backward 
    lemmas, and the other way around is also possible. For example: *)

Lemma neutral_l_of_monoid' : forall (A : Type) (M : monoid_str A),
  monoid M ->
  neutral_l (monoid_set M) (monoid_op M) (monoid_id M).
Proof using. introv HM. applys* neutral_l_of_monoid. Qed.

(** All we need is some tooling for generating one of the two versions, 
    because we certainly don't want to write two versions of each lemma
    by hand. *)


(* ---------------------------------------------------------------------- *)
(** Monoid over full types *)

(** [Z] is a communative monoid for [0] and [+]. In this monoid, the type [A] of elements
    is [Z], and the set [E] is all of [Z]. This pattern of having a structure
    over a full type is common, so it is worth introducing simplified, derived
    definitions for this case. *)

Record Monoid_str (A:Type) : Type := Monoid_ {
   Monoid_id : A;
   Monoid_op : A -> A -> A; }.

(** A monoid on a full type is a monoid on the set of all elements of that type *)

Definition set_full (A:Type) : set A :=
  set_st (fun (_:A) => True).

Coercion Monoid_of_monoid (A:Type) (M:Monoid_str A) : monoid_str A :=
  {| monoid_set := set_full A;
     monoid_id := Monoid_id M;
     monoid_op := Monoid_op M |}.

(** Properties for full operators *)

Definition Comm (A:Type) (f:A->A->A) : Prop := 
  forall x y, f x y = f y x.

Definition Assoc (A:Type) (f:A->A->A) : Prop := 
  forall x y z, f x (f y z) = f (f x y) z.

Definition Neutral_l (A:Type) (f:A->A->A) (e:A) : Prop :=
  forall x, f e x = x.

Definition Neutral_r (A:Type) (f:A->A->A) (e:A) : Prop :=
  forall x, f x e = x.

Definition Neutral_lr (A:Type) (f:A->A->A) (e:A) :=
  Neutral_l f e /\ Neutral_r f e.

(** Smart constructors *)

Lemma Monoid : forall (A:Type) (op : A->A->A) (id:A),
  Assoc op ->
  Neutral_lr op id ->
  monoid (Monoid_ id op).
Admitted.

Lemma comm_Monoid : forall (A:Type) (op : A->A->A) (id:A),
  let M := Monoid_ id op in
  monoid M ->
  Comm op ->
  comm_monoid M.
Admitted.

(** Demo: [Z] additive Monoid *)

Lemma example_Monoid_Z :
  comm_monoid (Monoid_ 0%Z Z.add).
Proof using.
  apply comm_Monoid.
  { apply Monoid; try split; intros_all; try omega. }
  { intros_all; try omega. }
Qed.

(** Extract properties from a full Monoid, backward search of the monoid *)

Lemma Assoc_of_Monoid : forall (A : Type) (op : A->A->A) (id:A),
  monoid (Monoid_ id op) ->
  Assoc op.
Proof using.
  introv [? ? HA ?]. simpls. intros x y z. applys HA;
   unfold set_full; rewrite* mem_set_st_eq.
Qed.

Lemma Neutral_l_of_Monoid : forall (A : Type) (op : A->A->A) (id:A),
  monoid (Monoid_ id op) ->
  Neutral_l op id.
Proof using.
  introv [? ? ? [HN ?]]. simpls. intros x. applys HN.
  unfold set_full. rewrite* mem_set_st_eq.
Qed.

Lemma Comm_of_comm_Monoid : forall (A : Type) (op : A->A->A) (id:A),
  comm_monoid (Monoid_ id op) ->
  Comm op.
Proof using.
  introv [? HA]. simpls. intros x y. applys HA;
   unfold set_full; rewrite* mem_set_st_eq.
Qed.

(** Extract properties from a full Monoid, forward application *)

Lemma Assoc_of_Monoid' : forall (A : Type) (M : Monoid_str A),
  monoid M ->
  Assoc (monoid_op M).
Proof using. introv HM. applys* Assoc_of_Monoid. Qed.

(** Demo: exploiting associativity of [Z.add], by triggering  
    the search of the monoid [example_Monoid_Z], added as hint. *)

Hint Resolve example_Monoid_Z.

Lemma example_Monoid_Z_assoc : forall x y z,
  Z.add x (Z.add y z) = Z.add (Z.add x y) z.
Proof using.
  intros. rewrite Assoc_of_Monoid. { eauto. } { eauto. }
Qed.

(** Demo: in fact, we don't even need to refer to the lemma [Assoc_of_Monoid].
    All we need to say in the proof script, is that we need [Assoc Z.add]. *)

Tactic Notation "rew" constr(E) :=
  asserts_rewrite E.

Hint Resolve Assoc_of_Monoid.

Lemma example_Monoid_Z_assoc' : forall x y z,
  Z.add x (Z.add y z) = Z.add (Z.add x y) z.
Proof using.
  intros. rew (Assoc Z.add). eauto. eauto.
Qed.

(** This example shows that we can mimic the mathematical writing of
    "by associativity of Z.add", through the tactic step [rew (Assoc Z.add)].
    We state the property needed, without expliciting where it comes from,
    because this information is easy to synthesize. At the same time, 
    observe that the information is not embedded with the operation [Z.add],
    it comes as an proof. This allows us to work directly with the core
    operations, without requiring complex wrappers around them. *)


(* ---------------------------------------------------------------------- *)
(** Lifting of results *)

(** The results on [Monoid] shown above could, presumably, be automatically generated
    from statements on monoids, simply by specializing the set to [set_full],
    and simplifying away hypotheses that are equivalent to [True]. *)

(** Reciprocally, given a monoid with elements of type [A] from a set [E], 
    we can define a [Monoid] over the [Type] that consists of only values
    that belong to the set [E]. Then, we can lift results that are proved
    for monoids over full types into results that hold for all monoids. *)

(** First, we dsecribe the conversion from an arbitrary monoid into a monoid
    acting over the [Type] made of exactly the set of elements that it operates over. *)

(** [typ E] denotes a [Type] made of the set values that belong to the set [E] *)

Definition typ (A:Type) (E:set A) : Type := 
  { x : A | x \in E }.

(** [typ_elem] converts an element form a set [E] into a value of type [typ E] *)

Program Definition typ_elem (A:Type) (E:set A) (x : A) (H : x \in E) : typ E :=
  exist _ x _.

(** [typ_op] converts a binary operation [A -> A -> A] that is internal to [E] 
    into a function of type [typ E -> typ E -> typ E]. *)

Program Definition typ_op (A:Type) (E:set A) (f : A -> A -> A) (H : set_op E f) 
                            : (typ E -> typ E -> typ E) :=
  (* intros [x Hx] [y Hy]. econstructor. apply (H x y Hx Hy). Defined. *)
  fun a b =>
    let (x,Hx) := a in
    let (y,Hy) := b in
    exist _ (f x y) _.

(** [typ_monoid] converts a monoid over expressed in a set [E], in a carried type [A],
    into a [Monoid] over the full type [typ E]. *)

Program Definition typ_monoid (A:Type) (M:monoid_str A) (H : monoid M)
                                 : Monoid_str (typ (monoid_set M)).
  destruct M as [E id op]. simpl.
  destruct H as [HA HB HC HD].
  constructor. applys typ_elem HA. applys typ_op HB.
Defined.

(** If [M] is a monoid, then so is [typ_monoid M]. *)
Lemma monoid_typ_monoid : forall (A:Type) (M:monoid_str A) (H : monoid M),
  monoid (typ_monoid H).
Proof using.
Admitted.

(** If [M] is a commutative monoid, then so is [typ_monoid M]. *)
Lemma comm_monoid_typ_monoid : forall (A:Type) (M:monoid_str A) (H : comm_monoid M),
  comm_monoid (typ_monoid (comm_monoid_monoid H)).
Proof using.
  intros A M [HM HC]. constructor; simpls.
  { applys monoid_typ_monoid. } 
  { destruct M as [E op id]. destruct HM as [? ? ? ?]. intros [x Ex] [y Ey] _ _. simpls.
    apply LibEqual.exist_eq_exist. rewrite* HC. }
Qed.


(** Let us show how a lemma proved about a [Monoid], that is, over a full type,
    can be translated into a lemma about all monoids. Consider the example
    of the combined commutativity-associativity property, written [Comm_Assoc]. *)

Definition Comm_Assoc (A:Type) (f:A->A->A) : Prop := 
  forall x y z, f x (f y z) = f z (f x y).

(** This property [Comm_Assoc] can be derived from commutativity and associativity. *)

Lemma Comm_Assoc_of_Comm_and_Assoc : forall (A:Type) (f:A->A->A),
  Comm f ->
  Assoc f ->
  Comm_Assoc f.
Proof using.
  introv HC HA. intros x y z. rewrite HA. rewrite HC. auto.
Qed.

(** The property [Comm_Assoc] thus holds in any commutative [Monoid]. *)

Lemma Comm_Assoc_of_comm_Monoid : forall (A : Type) (op : A->A->A) (id:A),
  comm_monoid (Monoid_ id op) ->
  Comm_Assoc op.
Proof using. 
  introv HM. applys Comm_Assoc_of_Comm_and_Assoc.
  { applys* Comm_of_comm_Monoid. }
  { applys* Assoc_of_Monoid. }
Qed.

(** Let us also state the variant lemma for forward usage. *)

Lemma Comm_Assoc_of_comm_Monoid' : forall (A : Type) (M : Monoid_str A),
  comm_monoid M ->
  Comm_Assoc (Monoid_op M).
Proof using. introv HM. applys* Comm_Assoc_of_comm_Monoid. Qed.


(** Consider now the combined commutativity-associativity over a set [E]. *)

Definition comm_assoc (A:Type) (E:set A) (f:A->A->A) : Prop := 
  forall_ x y z \in E, f x (f y z) = f z (f x y).

(** The property [comm_assoc E f] is derivable from [Comm_Assoc] over the
    full types of values that belong to the set [E]. *)

Lemma comm_assoc_of_Comm_Assoc : forall (A:Type) (E:set A) (f:A->A->A) (H : set_op E f),
  Comm_Assoc (typ_op H) ->
  comm_assoc E f.
Proof using.
  introv HCA. intros x y z Hx Hy Hz. 
  lets EQ: HCA (typ_elem Hx) (typ_elem Hy) (typ_elem Hz). inverts EQ. auto.
Qed.

(** We can thus derive from the lemma [Comm_Assoc_of_comm_Monoid] the fact that 
    [comm_assoc] holds in any commutative [monoid] over a set [E].
    The idea is to exploit the result for [Monoid] on the full type [typ E].
    My proof is a bit tedious at the moment, but I'm pretty sure it could be simplified. *)

Lemma Comm_assoc_of_comm_monoid' : forall (A : Type) (M : monoid_str A),
  comm_monoid M ->
  comm_assoc (monoid_set M) (monoid_op M).
Proof using.
  introv HM. lets HM':HM. 
  lets R: (comm_monoid_typ_monoid HM).
  destruct HM as [HR HCO].
  destruct HR as [HA HB HC HD]. 
  destruct M as [E id op]. simpls.
  eapply (@comm_assoc_of_Comm_Assoc _ _ _ HB).
  eapply Comm_Assoc_of_comm_Monoid. applys R.
Qed.

(** Variant for backward applications *)

Lemma comm_assoc_of_comm_Monoid : forall (A : Type) (E : set A) (op : A->A->A) (id:A),
  comm_monoid (monoid_ E id op) ->
  comm_assoc E op.
Proof using. introv HM. apply (Comm_assoc_of_comm_monoid' HM). Qed.

(** The full construction is a bit tedious to carry out by hand, but I guess it
    could be simplified, or even possibly automated with tool support. 
    
    In summary, the idea is that you can do complex proofs using [Monoid],
    using simple definitions for [Assoc], etc (not constrainted by a set [E]),
    then you can automatically export results on all [monoid]s. *)


(**************************************************************************)
(** * Overloading *)

(** I would like Coq to benefit from ADA and PVS style resolution of overloading.

    In those systems, resolution is directed both by the type of function arguments 
    and the type expected by the context, using a two-pass typing algorithm
    (bottom-up, then top-down). I will soon work on extending the
    algorithm form ADA and PVS to support polymorphism.

    For the moment, let me approximate this feature by using:
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

(** To avoid confusion with existing Coq scopes, I here use '0 and '+ symbols.
    But in the long term, I would write 0 and +. *)

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

Definition ZeroPlus_of_Monoid (A:Type) (M:Monoid_str A) : Zero A * Plus A A A :=
  (Zero_monoid M, Plus_monoid M).

(** Because I don't have printing for overloaded symbols, I currently use only-printing
    notations for additive monoids. *)

Declare Scope additive_monoid_scope.
Open Scope additive_monoid_scope.
Notation "'0" := (monoid_id _) (at level 0, only printing) : additive_monoid_scope.
Notation "'0" := (Monoid_id _) (at level 0, only printing) : additive_monoid_scope.
Notation "n '+ m" := (monoid_op _ n m) (at level 40, only printing) : additive_monoid_scope.
Notation "n '+ m" := (Monoid_op _ n m) (at level 40, only printing) : additive_monoid_scope.


(** "Let M(E,+,0) be a commutative monoid. 
    For any [x] in [E], we have ['0 '+ x = x]."
    This statement is translated as follows. *)

Lemma example_comm_monoid_notations :
  forall (A : Type) (M : monoid_str A), comm_monoid M ->
  let '(E,_,_) := SetZeroPlus_of_monoid M in
  forall_ x \in E,
  '0 '+ x = x.
Proof using.
  over. introv HM Hx.
 (* prints as [x '+ '0 = x] *)
 (* stands for [monoid_op M x (monoid_id M) = x] *)
  rewrites (>> neutral_l_of_monoid Hx).
  { eauto. } (* monoid_of_comm_monoid *)
  { eauto. } (* solves [x = x]. *)
Qed.

(** "Let M(+,0) be a commutative monoid over a full type [A] 
    For any [x] of type [A], we have ['0 '+ x = x]."
    This statement is translated as follows. *)

Lemma example_comm_Monoid_notations :
  forall (A : Type) (M : Monoid_str A), comm_monoid M ->
  let '(_,_) := ZeroPlus_of_Monoid M in
  forall x,
  '0 '+ x = x.
Proof using. 
  over. introv HM. intros x.
 (* prints as [x '+ '0 = x] *)
 (* stands for [monoid_op M x (monoid_id M) = x] *)
  rewrite Neutral_l_of_Monoid.
  { eauto. } (* solves [x = x]. *)
  { eauto. } (* monoid_of_comm_monoid *)
Qed.

(**  Assume the notation "forall (x st P), .."  means "forall x, P x -> ..".
     Assume that "0" can be viewed as a variable name (overloaded),
     and that "+", when it appears in the position of a binder,
     can be viewed as a a variable name alias for the operator "plus".
     We could write the previous statement as:

[[
Autoquantify (A : Type).
Implicit Types (M : Monoid_str A).

Lemma example_comm_Monoid :
  forall (M st comm_monoid), let (0,+) := M in
  forall x, '0 '+ x = x.
]]
*)

(**  We could even try to go further, using the "as" syntax from pattern matching:
[[
  forall ((0,+) as M st comm_monoid)
]]

or introduce a new syntax for "as", closer to the standard mathematical notation.
[[
  forall (M(0,+) st comm_monoid)
]]
*)





























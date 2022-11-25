(**************************************************************************
* TLC: A library for Coq                                                  *
* Demos for Containers, in particular finite maps                         *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
From TLC Require Import LibTactics LibLogic LibReflect LibOption
  LibRelation LibLogic LibOperation LibEpsilon LibMonoid LibSet
  LibContainer LibMap.

Local Open Scope set_scope.


(* ********************************************************************* *)
(** * Introduction *)

(* Assume a type of keys, call it [int] *)

Parameter int : Type.

(** Assume a type of values, called [val], that's inhabited. *)

Parameter val : Type.
Parameter Inhab_val : Inhab val.
#[global]
Existing Instance Inhab_val.


(* ********************************************************************** *)
(** * Basic usage of map operations *)

Module Basic.

(** We can use a map from [int] to [val], and read in that map *)

Definition my_read (m:map int val) (i:int) :=
  m[i].

(** We can also write a value in the map; it does not matter whether
    the key already existed or not. *)

Definition my_write (m:map int val) (i:int) (v:val) :=
  m[i := v].

(** To reason about a read, we can use the lemma [read_update]. *)

Lemma my_read_write : forall (m:map int val) (i j:int) (v:val),
  m[i := v][j] = (If i = j then v else m[j]).
Proof using.
  intros. rewrite read_update. auto.
Qed.

(** Sometimes we need to talk about the domain of a map.
    [dom m] is a [set] of keys, in the sense of LibSet's [set].
    For example, to assert that two maps have the same domain. *)

Definition my_same_dom (m1 m2:map int val) :=
  dom m1 = dom m2.

(** To assert that one key is valid for a domain, we use
    [i \in (dom m)], which is shortened to [i \indom m].
    The latter is a notation for [(x \in (dom m : set _))],
    with the annotation to help the typechecker. *)

Definition my_indom (m:map int val) (i:int) :=
  i \indom m.

(** Similarly, the notation [x \notindom m] is available. *)

(** In an inductive definition, it is commonplace to assert
    that [i] is in the domain of [m] and that [M[i] = v].
    The binds predicate captures the conjunction of these
    two facts. The definition can be unfolded using the
    following rewriting rule. *)

Parameter binds_eq_indom_read : forall A `{Inhab B} (M:map A B) x v,
  (binds M x v) = (x \indom M /\ M[x] = v).

(** Other operations on maps involve:
    - empty map [(\{} : map A B)]. The type annotation is often required.
    - union of maps [m1 \u m2]
    - removal of a set of keys [m \- E]
    - removal of a key [m \-- i], equivalent to [m \- \{i}]
    - map_reduce w.r.t. a function and a monoid, e.g.
      [fold (monoid_make plus zero) f m], which computes
      [f k1 v1 + f k2 v2 + ... + f kn vn + 0].
    - inclusion [m1 \c m2] is not yet defined, but should be soon. *)

(** Lemmas for reasoning about maps can be found in two places:
    in [LibMap.v] and in [LibContainer.v]. The latter contains
    generic lemmas, that are shared by several data structures,
    such as sets and maps. The typeclass mechanism used for the
    sharing is explained next. *)

End Basic.


(* ********************************************************************** *)
(** * Implementation of maps *)

Module Internal.

(** Finite maps are implemented using the typeclasses defined in
    LibContainer. The internal implementation is: *)

Definition map (A B : Type) := A -> option B.

(** The internal definition of [read] in a map is thus a function
    that applies the map to the index. When the result is [None]
    it returns an arbitrary value. *)

Definition read_impl A `{Inhab B} (M:map A B) (k:A) :=
  match M k with
  | None => arbitrary
  | Some v => v
  end.

(** Doing so requires the type [B] to be inhabited. Let's look at
    the error message that we get when trying to work with a map
    on a type that's not inhabited. *)

(* Uncomment below to see the error message, saying that an instance
   for [BagRead int ?B (map int B)]. The message does not say it,
   but it complains in fact that [Inhab B] could not be found.
   We'll understand why the message is like so further on. *)

(*
Definition my_failed_read B (m:map int B) (i:int) :=
  m[i].
*)

(** The notation [m[i]] is defined in [LibContainer.v] as
    [read m i]. *)

Notation "m [ i ]" := (read m i).

(** The operation [read] is a typeclass. It applies to any
    data structure of type [T] on which a read operation can
    be performed using keys of type [A] to extract a value of
    type [B]. *)

Class BagRead A B T := { read : T -> A -> B }.

(** Note that the type of [read] is:
    [forall A B T {I:BagRead A B T}, T -> A -> B].
    In other words, [read] must be applied to an
    "instance" of the typeclass [BagRead], and then
    the result is a read function for that instance.
    We'll see further on what this means. *)

(** The connection between [read_impl] for type [map] and
    the generic [read] operation is performed through an
    instance declaration: *)

#[global]
Instance read_inst : forall A `{IB:Inhab B}, BagRead A B (map A B).
Proof. constructor. applys (@read_impl A B IB). Defined.

(** In the light of this, let's inspect the interpretation of [m[i]].
    It means [@read int val (map int val) read_inst m i]. *)

Definition my_read (m:map int val) (i:int): val :=
  m[i].

(** You can activate [Set Printing All] or menu
    ["Display all level-level contents" from the view menu in CoqIDE]
    to see the low-level interpretation. *)

(*
Print my_read.
*)

(** What happens during type-checking is that [read_inst] gets
    automatically inferred by the typeclass mechanism, based on the
    type of [m]. In other words, before type inference, Coq sees:
    [@read _ _ _ _ m i]. From the type of [m], it deduces
    [@read _ _ (map int val) (_:BagRead _ _ (map int val)) m i].
    From typeclass resolution, it finds out that [read_inst] is the
    instance that could fill in the argument with type
    [BagRead _ _ (map int val)]. *)

(** Now, we can see that the instance inferred is
    [@LibMap.read_inst int val Inhab_val].
    This instance refers to the instance asserting that [val] is
    inhabited. When such an assumption about the result type cannot
    be found, then the [read_inst] instance cannot be synthesized. *)

(** We can investigate the resolution process manually as follows. *)

Lemma test_resolution_1 : BagRead int val (map int val).
Proof using. typeclass. (* short for: [eauto with typeclass_instances.] *) Qed.

Lemma test_resolution_2 : Inhab val.
Proof using. typeclass. Qed.

Lemma test_resolution_3 : forall B, Inhab B.
Proof using. intros. try typeclass. (* resolution fails *) Abort.

Lemma test_resolution_4 : BagRead int val (map int val).
Proof using. (* execute:
   debug eauto with typeclass_instances. *) Abort.

Lemma test_resolution_5 : forall B, BagRead int B (map int B).
Proof using.
  (* execute:

    intros.
    debug eauto with typeclass_instances.
    (* shows that eauto is stuck after [apply read_inst] *)
    apply read_inst.
    debug eauto with typeclass_instances.
    (* shows that eauto is stuck on this subgoal. *)


  *)
Abort.


(** The file [LibContainer.v] contains generic lemmas. For example
    [union_empty_r] asserts that [m \u \{} = m]. This lemma is
    stated for any data structure of type [T] that features an
    empty and a union operation. *)

Class Union_empty_r (T:Type) {BE: BagEmpty T} {BU: BagUnion T} :=
  { union_empty_r : forall X, union empty X = X }.

(** The proof that [map] validates the lemma [union_empty_r] is
    derived from the fact that it validates the lemma [union_empty_l]
    and commutativity of union *)

Global Instance union_empty_r_of_union_empty_l (T:Type) {BE: BagEmpty T} {BU: BagUnion T} :
  Union_empty_l -> Union_comm -> Union_empty_r.
Abort.

(** The proof that [map] validates [union_empty_l] is itself derived
    from another lemma, called [union_empty_l_of_in_union_eq_and_in_empty_eq].
    More details can be found in [LibContainerDemo], but it is not needed
    to understand the full setup to use the lemmas over maps.] *)

(** The point is that [rewrite union_empty_r] is a tactic that rewrites
    [m \u \{} = m] for any data structure [m] over which the statement
    of this equality makes sense. *)

End Internal.

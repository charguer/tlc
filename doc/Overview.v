
(************************************************************************)
(** * Documentation *)

(** 

  - doc/overview.txt (the present file) gives a tour of the key
    features of TLC.

  - doc/conventions.txt describes the naming conventions in use.

  - doc/files.txt gives the list of files that have been cleaned up
    according to the new conventions and that compile in v8.6.

    DISCLAIMER: only the files marked "stable" in "doc/StableFiles.txt"
    have been cleaned up to compile in v8.6 and follow the new conventions.

*)


(************************************************************************)
(** * Tactics *)

(** TLC exports a bunch of tactics, to enhance and complete those provided
    by default. All tactics are implemented in Ltac. Native implementation
    would certainly allow clearer and more efficient implementations.
    
    - most tactics are defined in [LibTactics.v],
    - a couple of tactics are generalized later in other files (grep for "::="),
    - a bunch of tactics are defined in other files (grep for "Ltac"), 
      mainly decision procedures for tautologies, inequalities, set equalities,... 

*)

(************************************************************************)
(** * Organization of the files *)

(** Appart from LibTactics, the main files are organized as follows:

  Logic

     LibAxioms
     LibEqual
     LibLogic
     LibOperation
     LibReflect
     LibEpsilon
     LibChoice
     LibOperation
     LibWf
     LibFix

  Base datatypes

     LibBool
     LibProd
     LibSum
     LibUnit
     LibOption
     LibString
     LibInt
     LibNat
     LibList*

  Relations and structures

     LibRelation
     LibMonoid
     LibOrder
     LibMin

  Containers

     LibContainer
     LibSet
     LibMap
     ...

*)


(************************************************************************)
(** * Logic *)

(** TLC relies on classical logic. The file [LibAxiom.v] exports 3 axioms:
    - functional extensionality (dependent version)
    - propositional extensionality 
    - indefinite description.

    All other classical logic results are derived from these axioms.
    See files [LibLogic.v], [LibEqual.v], [LibChoice] and [LibEpsilon.v]. 
    
    In particular, [LibLogic] exports strong classical logic, for deciding
    the truth of an arbitrary proposition.
*)

Lemma classicT : forall (P : Prop), {P} + {~ P}.
  
(** In practice, we use the notation [If P then v1 else v2] for introducing
    conditionals over propositions. *)

Notation "'If' P 'then' v1 'else' v2" :=
  (if (classicT P) then v1 else v2)
  (at level 200, right associativity) : type_scope.


(************************************************************************)
(** * Inhabited types *)

(** Inhabited types are very useful for two purposes:
    - to not overspecify the result of a partial function,
    - to apply the epsilon operator, e.g. to take the minimum of a set
      without providing a proof on the call site a proof that this set 
      is nonempty,
    - to invoke the optimal fixed point combinator provided by TLC,
      in order to show that the return type of a partial function is
      inhabited.

    The typeclass is defined as follows, in the classic way.
*)

Class Inhab (A:Type) : Prop :=
  { Inhab_intro : (exists (x:A), True) }.

(** All usual types are proved inhabited. *)

Instance Inhab_list : forall A, Inhab (list A).
Proof using. intros. apply (Inhab_of_val nil). Qed.

(** The value [arbitrary] can be used as a dummy value at any place
    where a value of an inhabited type is expected. This definition
    relies on the indefinite description axiom to turn the [exists]
    into a strong existential. *)

Definition arbitrary `{Inhab A} : A :=
  sig_val (@indefinite_description A _ Inhab_intro).

(** A partial function, such as [List.nth], is defined only over
    inhabited types. Its result for invalid indices is specified
    to be equal to the [arbitrary] value of that type. *)

Fixpoint nth_def A (d:A) (n:nat) (l:list A) : A :=
  match l with
  | nil => d
  | x::l' =>
     match n with
     | 0 => x
     | S n' => nth_def d n' l'
     end
  end.

Definition nth `{IA:Inhab A} := 
  nth_def arbitrary.


(************************************************************************)
(** * Dependent types *)

(** TLC tries to avoid dependent types altogether. Let's be precise, thought:

    - Proof terms involve dependently-typed terms. But these are not meant 
      to be written or read.
    - Strong sum, e.g. {P} + {~ P}, involves a dependent type, but TLC
      uses strong sums only in the statement of the [classicT] lemma.
    - Type-classes involve dependent types, but we view type-class as a
      simpler mechanism than general dependently-typed programming.

    In Coq in general, dependently-typed programming is sometimes unavoidable,
    e.g. for definining tricky partial recursive functions. However, thanks
    to classical logic and the use of the optimal fixed point combinator 
    defined in [LibFix.v], we are able to define such functions without the
    need for dependent types.
    
*) 


(************************************************************************)
(** * From boolean to propositions and back *)

(** In that classical logic setting, boolean and propositions become
    essentially isomorphic. On the one hand, any boolean can be viewed
    as a proposition, via the coercion [istrue]. *)

Coercion istrue (b : bool) : Prop := (b = true).

(** Reciprocally, any proposition can be turned into a boolean, using
    the operator [isTrue]. *)

Definition isTrue (P : Prop) : bool :=
  If P then true else false.

(** We illustrate the use of these two combinators in the context of
    specifying programs in Separation Logic. First, we show that it
    is useful to assert that the boolean output value of a function
    is equal to the boolean associated with the proposition [L = nil]. *)

Lemma is_empty_spec : forall (s:loc) (L:list A),
  app is_empty [s]
    PRE (s ~> Stack L)
    POST (fun (b:bool) => (s ~> Stack L) \* \[b = isTrue (L = nil)]).

(** The postcondition could also be stated [istrue b = (L = nil)],
    however the form [b = isTrue (L = nil)] is much more interesting
    because it allows for immediately substituting away [b] using
    the [subst] tactic. *)

(** The coercion [istrue] is probably less fundamental. It saves some
    noise. Consider the verification of an ML program of form 
    [if b1 && !b2 then t1 else t2]. In the first branch of its analysis,
    it is convenient to view the assumption [b1 && !b2] instead of
    [(b1 && !b2) = true]. Moreover, the existence of a named coercion
    [istrue (b1 && !b2)] helps guiding the autorewrite tactic [rew_istrue]
    that we use to normalize the expression to [istrue b1 /\ ~ istrue b2],
    which is displayed as [b1 /\ ~ b2]. *)


(************************************************************************)
(** * Simplification by normalizing rewrite operations *)

(** In TLC, the [simpl] tactic is used as little as possible, for two
    reasons. First, its behavior is unspecified and is hard to control
    in practice. Often, one ends up with too much unfolding. Second,
    [simpl] does not work on operators that come from functor argumetns
    or that we wish to make abstract. 
    
    Instead, TLC relies heavily on simplification by iterated rewriting,
    using the [autorewrite] tactic. For example, [rew_list] is a tactic
    for normalizing [list] operations, with respect to a base of rewriting
    lemma. The rule is that the set of lemmas in a rewriting base should
    always be terminating and (whenever possible) confluent. This makes
    the rewriting tactic robust with respect to the order in which the
    rewriting lemmas are considered. *)

Hint Rewrite app_cons_l app_nil_l app_nil_r app_assoc
  app_cons_one_r length_nil length_cons length_app ... : rew_list.

(** It is very unfortunate that, in the current version of Coq, we need
    to manually define shorthands for each rewriting base...
    Fortunately, a patch or plugin could easily resolve the issue. *)

Tactic Notation "rew_list" :=
  autorewrite with rew_list.
Tactic Notation "rew_list" "in" "*" :=
  autorewrite with rew_list in *.
Tactic Notation "rew_list" "in" hyp(H) :=
  autorewrite with rew_list in H.


(************************************************************************)
(** * Executable versions of definitions *)

(** TLC makes no effort at providing definitions that compute within Coq.
    We believe that such attempt is doomed. 
    - Definitions that compute (or compute efficiently) are usually more
      complex than their non-constructive counterpart; yet, we'd like our
      definitions to always be as simple as possible, especially when they
      are part of the trusted base.
    - The ability to compute may require additional arguments, e.g. a 
      comparison relation for sets, making the structure very heavy to use
      (when not impossible to use, e.g. a set defined as a functor prevents
      the specification of a polymorphic-recursive function in terms of a set),
      and drifting far away from standard mathematics.
    - For some partial recursive functions, the only way to define a computable
      function is to involve dependent types, for justifying termination on the
      domain. In the end, the function obtained computes very inefficiently.
      One would rather have a clean non-computable function, and a 
      provably-equivalent function that simply caps its recursion depth.
*) 

(** The plan (which is not yet implemented inside TLC) is that for every 
    function, one may define a computable counterpart, either by hand or
    using the help of some generator. Such generator may be implemented
    using typeclasses, thought with some limitations, or may be implemented
    as a external plugin (as done e.g. in Isabelle/HOL). 
    
    For example, [LibList.mem x l] is an inductively-defined proposition 
    indicating whether the list [l] contains the element [x]. And
    [LibListX.mem x l] is a function that computes a boolean value 
    indicating whether [x] belongs to [l], assuming the type of the elements
    feature a boolean comparison function for deciding equality. 
    The lemma [LibListX.mem_eq] asserts: 
    [forall `{Comparable A} (x:A) (l:list A), 
      LibListX.mem_eq x l = isTrue (LibList.mem x l)]
    
    This lemmas allows to reason about code that computes using the executable
    version, using all the lemmas that hold about the logical function.
*)    


(************************************************************************)
(** * Overloading *)

(** Overloading of operators is implemented using typeclasses, 
    in particular for:
    - comparison operators (e.g. le, gt, etc...)
    - container operations (e.g. union, read in a map, etc..)

    and typeclasses are also used for all lemmas about these operations.

    In the long run, we plan to also use typeclasses for base types
    such as [nat] and [int]. However, due to inefficiencies in the
    current support for typeclasses, it would be too slow to use
    typeclasses in the current version of Coq for describing all basic
    arithmetic expressions. Thus, we stick to the traditional Coq 
    approach, which is to rely on the scope mechanism to overload 
    arithmetic operators.

*)


(************************************************************************)
(** * Order relations *)

(** See [LibOrder.v] and [LibSet.v] *)


(************************************************************************)
(** * Containers *)

(** See [LibContainer.v] and [Lib] *)


(************************************************************************)
(** * Fixed points *)

(** See [LibFixDemos.v] and [LibFix.v] and the corresponding paper. *)


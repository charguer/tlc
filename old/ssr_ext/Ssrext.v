(**************************************************************************
* Additional tactics for Coq+SSReflect                                    *
* Arthur Chargueraud                                                      *
* Distributed under the terms of the Cecil-B license                      *
***************************************************************************)

Set Implicit Arguments.



(* ********************************************************************** *)
(** * Tools for programming with Ltac *)

(* ---------------------------------------------------------------------- *)
(** ** Identity continuation *)

Ltac idcont tt := 
  idtac.

(* ---------------------------------------------------------------------- *)
(** ** Untyped arguments for tactics *)

(** Any Coq value can be boxed into the type [Boxer]. This is
    useful to use Coq computations for implementing tactics. *)

Inductive Boxer : Type :=
  | boxer : forall (A:Type), A -> Boxer.


(* ---------------------------------------------------------------------- *)
(** ** Optional arguments for tactics  *)

(** [ltac_no_arg] is a constant that can be used to simulate 
    optional arguments in tactic definitions. 
    Use [mytactic ltac_no_arg] on the tactic invokation,
    and use [match arg with ltac_no_arg => ..] or
    [match type of arg with ltac_No_arg  => ..] to
    test whether an argument was provided. *)

Inductive ltac_No_arg : Set := 
  | ltac_no_arg : ltac_No_arg.


(* ---------------------------------------------------------------------- *)
(** ** Wildcard arguments for tactics  *)

(** [ltac_wild] is a constant that can be used to simulate 
    wildcard arguments in tactic definitions. Notation is [__]. *)

Inductive ltac_Wild : Set := 
  | ltac_wild : ltac_Wild.

Notation "'__'" := ltac_wild : ltac_scope.

(** [ltac_wilds] is another constant that is typically used to
    simulate a sequence of [N] wildcards, with [N] chosen 
    appropriately depending on the context. Notation is [___]. *)

Inductive ltac_Wilds : Set := 
  | ltac_wilds : ltac_Wilds.

Notation "'___'" := ltac_wilds : ltac_scope.

Open Scope ltac_scope.


(* ---------------------------------------------------------------------- *)
(** ** Position markers *)

(** [ltac_Mark] and [ltac_mark] are dummy definitions used as sentinel
    by tactics, to mark a certain position in the context or in the goal. *)

Inductive ltac_Mark : Type :=
  | ltac_mark : ltac_Mark.

(** [gen_until_mark] repeats [generalize] on hypotheses from the 
    context, starting from the bottom and stopping as soon as reaching
    an hypothesis of type [Mark]. If fails if [Mark] does not
    appear in the context. *)

Ltac gen_until_mark :=
  match goal with H: ?T |- _ =>
  match T with 
  | ltac_Mark => clear H
  | _ => generalize H; clear H; gen_until_mark
  end end.

(** [intro_until_mark] repeats [intro] until reaching an hypothesis of
    type [Mark]. It throws away the hypothesis [Mark]. 
    It fails if [Mark] does not appear as an hypothesis in the 
    goal. *)

Ltac intro_until_mark :=
  match goal with 
  | |- (ltac_Mark -> _) => intros _
  | _ => intro; intro_until_mark
  end.


(* ---------------------------------------------------------------------- *)
(** ** List of arguments for tactics  *)

(** A datatype of type [list Boxer] is used to manipulate list of
    Coq values in ltac. Notation is [>> v1 v2 ... vN] for building
    a list containing the values [v1] through [vN]. *)
(** ==> will be subsumed by "$" notation in the future. *)

Require Import List.

Notation "'>>'" :=
  (@nil Boxer)
  (at level 0)
  : ltac_scope.
Notation "'>>' v1" :=
  ((boxer v1)::nil)
  (at level 0, v1 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2" :=
  ((boxer v1)::(boxer v2)::nil)
  (at level 0, v1 at level 0, v2 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::(boxer v12)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
   v12 at level 0)
  : ltac_scope.
Notation "'>>' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13" :=
  ((boxer v1)::(boxer v2)::(boxer v3)::(boxer v4)::(boxer v5)
   ::(boxer v6)::(boxer v7)::(boxer v8)::(boxer v9)::(boxer v10)
   ::(boxer v11)::(boxer v12)::(boxer v13)::nil)
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
   v12 at level 0, v13 at level 0)
  : ltac_scope.


(** The tactic [list_boxer_of] inputs a term [E] and returns a term 
    of type "list boxer", according to the following rules:
    - if [E] is already of type "list Boxer", then it returns [E];
    - otherwise, it returns the list [(boxer E)::nil]. *)

Ltac list_boxer_of E := 
  match type of E with 
  | List.list Boxer => constr:(E)
  | _ => constr:((boxer E)::nil)
  end.

(* ---------------------------------------------------------------------- *)
(** ** Tagging of hypotheses *)

(** [ltac_tag_subst] is a specific marker for hypotheses 
    which is used to tag hypotheses that are equalities to 
    be substituted. *)

Definition ltac_tag_subst (A:Type) (x:A) := x.

(** [ltac_to_generalize] is a specific marker for hypotheses 
    to be generalized. *)

Definition ltac_to_generalize (A:Type) (x:A) := x.

Ltac gen_to_generalize :=
  repeat match goal with 
    H: ltac_to_generalize _ |- _ => generalize H; clear H end.

Ltac mark_to_generalize H :=
  let T := type of H in
  change T with (ltac_to_generalize T) in H.


(* ---------------------------------------------------------------------- *)
(** ** An alias for [eq] *)

(** [eq'] is an alias for [eq] to be used for equalities in 
    inductive definitions, so that they don't get mixed with
    equalities generated by [inversion]. *)

Definition eq' := @eq. 

Hint Unfold eq'.

Notation "x '='' y" := (@eq' _ x y) 
  (at level 70, y at next level).


(* ---------------------------------------------------------------------- *)
(** ** Instantiation and forward-chaining *)

(** The instantiation tactics are used to instantiate a lemma [E]
    (whose type is a product) on some arguments. The type of [E] is
    made of implications and universal quantifications, e.g.
    [forall x, P x -> forall y z, Q x y z -> R z].
    
    The first possibility is to provide arguments in order: first [x],
    then a proof of [P x], then [y] etc... In this mode, called "Args",
    all the arguments are to be provided. If a wildcard is provided
    (written [__]), then an existential variable will be introduced in
    place of the argument.

    It is very convenient to give some arguments the lemma should be
    instantiated on, and let the tactic find out automatically where
    underscores should be insterted. Underscore arguments [__] are
    interpret as follows: an underscore means that we want to skip the
    argument that has the same type as the next real argument provided
    (real means not an underscore). If there is no real argument after 
    underscore, then the underscore is used for the first possible argument.
   
    The general syntax is [tactic (>> E1 .. EN)] where [tactic] is
    the name of the tactic (possibly with some arguments) and [Ei]
    are the arguments. Moreover, some tactics accept the syntax
    [tactic E1 .. EN] as short for [tactic (>> E1 .. EN)] for
    values of [N] up to 5.

    Finally, if the argument [EN] given is a triple-underscore [___],
    then it is equivalent to providing a list of wildcards, with
    the appropriate number of wildcards. This means that all
    the remaining arguments of the lemma will be instantiated. 
    Definitions in the conclusion are not unfolded in this case. *)

(* Underlying implementation *)

Ltac app_assert t P cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ | cont(t H); clear H ].

Ltac app_evar t A cont :=
  let x := fresh "TEMP" in
  evar (x:A); 
  let t' := constr:(t x) in
  let t'' := (eval unfold x in t') in
  subst x; cont t''.

Ltac app_arg t P v cont := 
  let H := fresh "TEMP" in
  assert (H : P); [ apply v | cont(t H); try clear H ].

Ltac boxerlist_next_type vs :=
  match vs with
  | nil => constr:(ltac_wild)
  | (boxer ltac_wild)::?vs' => boxerlist_next_type vs'
  | (boxer ltac_wilds)::_ => constr:(ltac_wild)
  | (@boxer ?T _)::_ => constr:(T)
  end.

Ltac app_typeclass t cont :=
  let t' := constr:(t _) in
  cont t'.

Ltac build_app_alls t final :=
  let rec go t :=
    match type of t with 
    | ?P -> ?Q => app_assert t P go
    | forall _:?A, _ => 
        first [ app_evar t A go
              | app_typeclass t go
              | fail 3 ]
    | _ => final t
    end in 
  go t.

Ltac build_app_hnts t vs final :=
  let rec go t vs :=
    match vs with
    | nil => first [ final t | fail 1 ]
    | (boxer ltac_wilds)::_ => first [ build_app_alls t final | fail 1 ]
    | (boxer ?v)::?vs' => 
      let cont t' := go t' vs in
      let cont' t' := go t' vs' in
      let T := type of t in 
      let T := eval hnf in T in
      match v with
      | ltac_wild => 
         first [ let U := boxerlist_next_type vs' in
           match U with
           | ltac_wild =>
             match T with  
             | ?P -> ?Q => first [ app_assert t P cont' | fail 3 ]
             | forall _:?A, _ => first [ app_typeclass t cont'
                                       | app_evar t A cont' 
                                       | fail 3 ] 
             end 
           | _ =>
             match T with  (* should test T for unifiability *)
             | U -> ?Q => first [ app_assert t U cont' | fail 3 ]
             | forall _:U, _ => first 
                 [ app_typeclass t cont'
                 | app_evar t U cont' 
                 | fail 3 ] 
             | ?P -> ?Q => first [ app_assert t P cont | fail 3 ]
             | forall _:?A, _ => first 
                 [ app_typeclass t cont
                 | app_evar t A cont
                 | fail 3 ] 
             end 
           end
         | fail 2 ]
      | _ => 
          match T with
          | ?P -> ?Q => first [ app_arg t P v cont'
                              | app_assert t P cont
                              | fail 3 ]
           | forall _:Type, _ => 
              match type of v with 
              | Type => first [ cont' (t v) 
                              | app_evar t Type cont
                              | fail 3 ]
              | _ => first [ app_evar t Type cont
                           | fail 3 ]
              end 
          | forall _:?A, _ => 
             let V := type of v in
             match type of V with
             | Prop => first [ app_typeclass t cont
                              | app_evar t A cont
                              | fail 3 ]
             | _ => first [ cont' (t v) 
                          | app_typeclass t cont
                          | app_evar t A cont
                          | fail 3 ]
             end
          end
      end
    end in
  go t vs.
  (* todo: use local function for first [...] *)

Ltac build_app args final := 
  first [ 
    match args with (@boxer ?T ?t)::?vs => 
      let t := constr:(t:T) in
      build_app_hnts t vs final
    end
  | fail 1 "Instantiation fails for:" args].

Ltac unfold_head_until_product T :=
  eval hnf in T.

Ltac args_unfold_head_if_not_product args :=
  match args with (@boxer ?T ?t)::?vs => 
    let T' := unfold_head_until_product T in
    constr:((@boxer T' t)::vs)
  end. 

Ltac args_unfold_head_if_not_product_but_params args :=
  match args with 
  | (boxer ?t)::(boxer ?v)::?vs => 
     args_unfold_head_if_not_product args
  | _ => constr:(args)
  end.


(* ---------------------------------------------------------------------- *)
(** ** Lets tactic *)

(** [lets (>> E0 E1 .. EN)] will instantiate lemma [E0]
    on the arguments [Ei] (which may be wildcards [__]),
    and generalize the resulting term into the goal.

    Syntax [lets E0 E1 .. EN] is also available. If the last
    argument [EN] is [___] (triple-underscore), then all
    arguments of [H] will be instantiated, like with forwards. *)

Ltac lets_build Ei :=
  let args := list_boxer_of Ei in 
  let args := args_unfold_head_if_not_product_but_params args in
  (* let Ei''' := args_unfold_head_if_not_product Ei'' in*)
  build_app args ltac:(fun R => generalize R).

Tactic Notation "lets" constr(E) :=
  lets_build E.
Tactic Notation "lets" constr(E0) 
 constr(A1) :=
  lets (>> E0 A1).
Tactic Notation "lets" constr(E0) 
 constr(A1) constr(A2) :=
  lets (>> E0 A1 A2).
Tactic Notation "lets" constr(E0) 
 constr(A1) constr(A2) constr(A3) :=
  lets (>> E0 A1 A2 A3).
Tactic Notation "lets"constr(E0) 
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  lets (>> E0 A1 A2 A3 A4).
Tactic Notation "lets" constr(E0) 
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  lets (>> E0 A1 A2 A3 A4 A5).


(* ---------------------------------------------------------------------- *)
(** ** Forwards tactic *)

(** [forwards (>> E0 E1 .. EN)] is short for 
    [lets (>> E0 E1 .. EN ___)]. 
    The arguments [Ei] can be wildcards [__] (except [E0]).
    [H] may be an introduction pattern, or a sequence of
    introduction pattern, or empty. 
    Syntax [forwards E0 E1 .. EN] is also available. *)

Ltac forwards_build_app_arg Ei :=
  let args := list_boxer_of Ei in
  let args := (eval simpl in (args ++ ((boxer ___)::nil))) in
  let args := args_unfold_head_if_not_product args in
  args.

Ltac forwards_then Ei cont :=
  let args := forwards_build_app_arg Ei in 
  let args := args_unfold_head_if_not_product_but_params args in
  build_app args cont.

Tactic Notation "forwards" constr(Ei) :=
  let args := forwards_build_app_arg Ei in 
  lets args. 

Tactic Notation "forwards" constr(E0) 
 constr(A1) :=
  forwards (>> E0 A1).
Tactic Notation "forwards" constr(E0) 
 constr(A1) constr(A2) :=
  forwards (>> E0 A1 A2).
Tactic Notation "forwards" constr(E0) 
 constr(A1) constr(A2) constr(A3) :=
  forwards (>> E0 A1 A2 A3).
Tactic Notation "forwards" constr(E0) 
 constr(A1) constr(A2) constr(A3) constr(A4) :=
  forwards (>> E0 A1 A2 A3 A4).
Tactic Notation "forwards" constr(E0) 
 constr(A1) constr(A2) constr(A3) constr(A4) constr(A5) :=
  forwards (>> E0 A1 A2 A3 A4 A5).


(* ---------------------------------------------------------------------- *)
(** ** Flexible tactic *)

(** The tactic [flexible] replaces a goal of the form
    [P x y z] with a goal of the form [P x ?a z] and a
    subgoal [?a = y]. The introduction of the evar [?a] makes
    it possible to apply lemmas that would not apply to the
    original goal, for example a lemma of the form 
    [forall n m, P n n m], because [x] and [y] might be equal
    but not convertible.
    
    Usage is [flexible i1 ... ik], where the indices are the
    positions of the arguments to be replaced by evars, 
    ----counting from the right-hand side-----. If [0] is given as
    argument, then the entire goal is replaced by an evar. *)

Section FlexibleLemma.
Variables (A0 A1 : Type).
Variables (A2 : forall (x1 : A1), Type).
Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).
Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).
Variables (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type).
Variables (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

Lemma flexible_0 : forall (P Q:Prop),
  P -> P = Q -> Q.
Proof. intros. subst. auto. Qed.

Lemma flexible_1 : 
  forall (P:A0->Prop) x1 y1,
  P y1 -> x1 = y1 -> P x1.
Proof. intros. subst. auto. Qed.

Lemma flexible_2 : 
  forall y1 (P:A0->forall(x1:A1),Prop) x1 x2,
  P y1 x2 -> x1 = y1 -> P x1 x2.
Proof. intros. subst. auto. Qed.

Lemma flexible_3 : 
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1),Prop) x1 x2 x3,
  P y1 x2 x3 -> x1 = y1 -> P x1 x2 x3.
Proof. intros. subst. auto. Qed.

Lemma flexible_4 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2),Prop) x1 x2 x3 x4,
  P y1 x2 x3 x4 -> x1 = y1 -> P x1 x2 x3 x4.
Proof. intros. subst. auto. Qed.

Lemma flexible_5 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3),Prop) x1 x2 x3 x4 x5,
  P y1 x2 x3 x4 x5 -> x1 = y1 -> P x1 x2 x3 x4 x5.
Proof. intros. subst. auto. Qed.

Lemma flexible_6 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3)(x5:A5 x4),Prop) 
  x1 x2 x3 x4 x5 x6,
  P y1 x2 x3 x4 x5 x6 -> x1 = y1 -> P x1 x2 x3 x4 x5 x6.
Proof. intros. subst. auto. Qed.

End FlexibleLemma.

Ltac flexible_lemma n :=
  match (*nat_from_number*) n with
  | 0 => constr:(flexible_0)
  | 1 => constr:(flexible_1)
  | 2 => constr:(flexible_2)
  | 3 => constr:(flexible_3)
  | 4 => constr:(flexible_4)
  | 5 => constr:(flexible_5)
  | 6 => constr:(flexible_6)
  end.  

Ltac flexible_one n :=
  let L := flexible_lemma n in
  eapply L.

Ltac flexible_several E cont :=
  let all_pos := match type of E with 
    | List.list Boxer => constr:(E)
    | _ => constr:((boxer E)::nil)
    end in
  let rec go pos :=
     match pos with
     | nil => cont tt
     | (boxer ?n)::?pos' => flexible_one n; [ instantiate; go pos' | ]
     end in
  go all_pos.

Tactic Notation "flexible" constr(E) :=
  flexible_several E ltac:(fun _ => idtac).
Tactic Notation "flexible" constr(n1) constr(n2) :=
  flexible (>> n1 n2).
Tactic Notation "flexible" constr(n1) constr(n2) constr(n3) :=
  flexible (>> n1 n2 n3).
Tactic Notation "flexible" constr(n1) constr(n2) constr(n3) constr(n4) :=
  flexible (>> n1 n2 n3 n4).


(* ---------------------------------------------------------------------- *)
(** * Common tactics for simplifying goals like [intuition] *)

Ltac jauto_set_hyps :=
  repeat match goal with H: ?T |- _ => 
    match T with
    | _ /\ _ => destruct H
    | exists a, _ => destruct H 
    | _ => generalize H; clear H
    end
  end.

Ltac jauto_set_goal :=
  repeat match goal with
  | |- exists a, _ => esplit
  | |- _ /\ _ => split
  end.

Ltac jauto_set :=
  intros; jauto_set_hyps; 
  intros; jauto_set_goal;
  unfold not in *.


(* ---------------------------------------------------------------------- *)
(** ** Absurd goals *)

(** [false_goal] replaces any goal by the goal [False]. 
    Contrary to the tactic [false] (below), it does not try to do
    anything else *)

Tactic Notation "false_goal" :=
  elimtype False.

(** [false_post] is the underlying tactic used to prove goals
    of the form [False]. In the default implementation, it proves
    the goal if the context contains [False] or an hypothesis of the
    form [C x1 .. xN  =  D y1 .. yM], or if the [congruence] tactic
    finds a proof of [x <> x] for some [x]. *) 

Ltac false_post :=
  solve [ assumption | discriminate | congruence ].

(** [false] replaces any goal by the goal [False], and calls [false_post] *)

Tactic Notation "false" :=
  false_goal; try false_post.

(** [tryfalse] tries to solve a goal by contradiction, and leaves
    the goal unchanged if it cannot solve it.
    It is equivalent to [try solve \[ false \]]. *)

Tactic Notation "tryfalse" :=
  try solve [ false ].

(** [false E] tries to exploit lemma [E] to prove the goal false.
    [false E1 .. EN] is equivalent to [false (>> E1 .. EN)],
    which tries to apply [applys (>> E1 .. EN)] and if it
    does not work then tries [forwards H: (>> E1 .. EN)]
    followed with [false] *)

Ltac false_then E  :=
  false_goal; first
  [ eapply E; instantiate
  | forwards_then E ltac:(fun M => 
      pose M; jauto_set_hyps; intros; false) ].

Tactic Notation "false" constr(E) :=
  false_then E.
Tactic Notation "false" constr(E) constr(E1) :=
  false (>> E E1).
Tactic Notation "false" constr(E) constr(E1) constr(E2) :=
  false (>> E E1 E2).
Tactic Notation "false" constr(E) constr(E1) constr(E2) constr(E3) :=
  false (>> E E1 E2 E3).
Tactic Notation "false" constr(E) constr(E1) constr(E2) constr(E3) constr(E4) :=
  false (>> E E1 E2 E3 E4).



(* ---------------------------------------------------------------------- *)
(** ** Unfolding *)

(** [unfolds] unfolds the head definition in the goal, i.e. if the
    goal has form [P x1 ... xN] then it calls [unfold P].
    If the goal is an equality, it tries to unfold the head constant
    on the left-hand side, and otherwise tries on the right-hand side.
    If the goal is a product, it calls [intros] first.
    -- warning: this tactic is overriden in LibReflect. *)

Ltac get_head E :=
  match E with
  | ?P _ _ _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ _ _ => constr:(P)  
  | ?P _ _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ _ => constr:(P)
  | ?P _ _ _ _ _ => constr:(P)  
  | ?P _ _ _ _ => constr:(P)  
  | ?P _ _ _ => constr:(P) 
  | ?P _ _ => constr:(P)  
  | ?P _ => constr:(P)
  | ?P => constr:(P)
  end.

Ltac apply_to_head_of E cont :=
  let go E :=  
    let P := get_head E in cont P in
  match E with
  | forall _,_ => intros; apply_to_head_of E cont
  | ?A = ?B => first [ go A | go B ]
  | ?A => go A 
  end.

Ltac unfolds_base :=
  match goal with |- ?G => 
   apply_to_head_of G ltac:(fun P => unfold P) end.

Tactic Notation "unfolds" :=
  unfolds_base.


(* ---------------------------------------------------------------------- *)
(** ** Basic inversion *)

(** [invert H] is same to [inversion H; clear H] except that it puts 
    all the facts obtained in the goal. *)
(** [inverts keep H] is same but does not clear H. *)

Tactic Notation "invert" "keep" hyp(H) :=
  pose ltac_mark; inversion H; gen_until_mark.

Tactic Notation "invert" hyp(H) :=
  invert keep H; clear H.



(* ---------------------------------------------------------------------- *)
(** ** Inversion with substitution *)

(** [inverts H] is same to [inversion H; clear H] except that it puts 
    all the facts obtained in the goal AND substitutes all equalities
    that have been generated. *)

(** Our inversion tactics is able to get rid of dependent equalities
    generated by [inversion], using proof irrelevance.
    If you do not want this axiom, write instead:
      Axiom inj_pair2 : True. *)

Axiom inj_pair2 : forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
       existT P p x = existT P p y -> x = y.
  (* Proof using. apply Eqdep.EqdepTheory.inj_pair2. Qed.*)

Ltac get_last_hyp tt :=
  match goal with H: _ |- _ => constr:(H) end.

Ltac inverts_tactic H :=
  let rec go tt :=
    match goal with 
    | |- (ltac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H; 
                           first [ subst x | subst y ]; 
                           go tt
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh in intro H; 
         generalize (@inj_pair2 _ P p x y H);
         clear H; go tt
    | |- (forall _, _) => 
       intro; let H := get_last_hyp tt in mark_to_generalize H; go tt
    end in
  pose ltac_mark; inversion H; 
  generalize ltac_mark; gen_until_mark; 
  go tt; gen_to_generalize; unfold ltac_to_generalize in *;
  unfold eq' in *.

Tactic Notation "inverts" "keep" hyp(H) :=
  inverts_tactic H.

(** [inverts keep H] is same but does not clear H. *)

Tactic Notation "inverts" hyp(H) :=
  inverts_tactic H; clear H.


(* ---------------------------------------------------------------------- *)
(** ** Generalization *)

(** [gen X1 .. XN] is a shorthand for calling [generalize dependent] 
    successively on variables [XN]...[X1]. Note that the variables
    are generalized in reverse order, following the convention of
    the [generalize] tactic: it means that [X1] will be the first
    quantified variable in the resulting goal. *) 
(* ==> could become "move: !x" or something similar in ssr *)

Tactic Notation "gen" ident(X1) :=
  generalize dependent X1.
Tactic Notation "gen" ident(X1) ident(X2) :=
  gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) :=
  gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4)  :=
  gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) :=
  gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) 
 ident(X6) :=
  gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) 
 ident(X6) ident(X7) :=
  gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) 
 ident(X6) ident(X7) ident(X8) :=
  gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) 
 ident(X6) ident(X7) ident(X8) ident(X9) :=
  gen X9; gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.
Tactic Notation "gen" ident(X1) ident(X2) ident(X3) ident(X4) ident(X5) 
 ident(X6) ident(X7) ident(X8) ident(X9) ident(X10) :=
  gen X10; gen X9; gen X8; gen X7; gen X6; gen X5; gen X4; gen X3; gen X2; gen X1.



(* ---------------------------------------------------------------------- *)
(** ** Clearing hypotheses *)

(** [clears X1 ... XN] is a variation on [clear] which clears
    the variables [X1]..[XN] as well as all the hypotheses which
    depend on them. Contrary to [clear], it never fails. *)

Tactic Notation "clears" ident(X1) :=
  let rec doit _ :=
  match goal with 
  | H:context[X1] |- _ => clear H; try (doit tt)
  | _ => clear X1
  end in doit tt.
Tactic Notation "clears" ident(X1) ident(X2) :=
  clears X1; clears X2.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) :=
  clears X1; clears X2; clears X3.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4) :=
  clears X1; clears X2; clears X3; clears X4.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4) 
 ident(X5) :=
  clears X1; clears X2; clears X3; clears X4; clears X5.
Tactic Notation "clears" ident(X1) ident(X2) ident(X3) ident(X4)
 ident(X5) ident(X6) :=
  clears X1; clears X2; clears X3; clears X4; clears X5; clears X6.


(* ---------------------------------------------------------------------- *)
(** ** [jauto], a new automation tactics *)

(** [jauto] is better at [intuition eauto] because it can open existentials
    from the context. In the same time, [jauto] can be faster than 
    [intuition eauto] because it does not destruct disjunctions from the 
    context. The strategy of [jauto] can be summarized as follows:
    - open all the existentials and conjunctions from the context
    - call esplit and split on the existentials and conjunctions in the goal
    - call eauto. *)

Tactic Notation "jauto" :=
  try solve [ jauto_set; eauto ].

Tactic Notation "jauto_fast" :=
  try solve [ auto | eauto | jauto ].


(* ---------------------------------------------------------------------- *)
(** ** Constructor *)

(** [constr] calls [econstructor]; 
    later it will call [exactly_once econstructor], which verifies
    that only one constructor can be applied. *)

Tactic Notation "constr" :=
  econstructor; unfold eq'.




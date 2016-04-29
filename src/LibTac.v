(*

Lemma test : forall (P:Prop),
  P -> (forall n:nat, n > 0 -> P -> True) -> True.
intros P HP H.

evar (x : nat) ; evar (Q : x > 0) ;
let E := constr:(H x) in
let F := constr:(E Q) in
let G := constr:(F HP) in
let v := eval cbv delta [x Q] in G in
let v := match v with context [?C] => is_evar C ; idtac C ; fail 0 | _ => constr:(0%nat) end in
idtac v.


  refine F.

  evar (x:nat); evar(P:x>0);
  let E := uconstr:(H x) in
  let F := uconstr:(E P) in
  refine F. pattern x.






Definition argindex(t : Type)(Admit : forall T, T) : t.
Proof.
  intros.
  apply Admit.
Qed.

Ltac remove_argindexes n f :=
  match f with
  | context[?C] =>
    lazymatch C with
      (argindex (let a := n in ?T) _) =>
      lazymatch (eval pattern C in f) with
        ?F _ =>
        constr:(ltac:(
                  (*Try renaming any hyp a so that there is no clash.  The
                  rename will not be visible outside this constr.*)
                  tryif is_var a then (let a' := fresh in rename a into a') else idtac;
                  let r := constr:(
                            fun (a : T) =>
                              ltac:(let b := (eval cbn beta in (F a)) in
                                    let r := remove_argindexes (S n) b in
                                    exact r)) in exact r))
      end
    end
  | context[?C] =>
    (*If the above case failed, it was probably because of a clash between a
    and something in T.  One would not expect this to happen, considering how
    a encloses T without binding anything in it, but it does for some
    reason.  Probably a Coq bug?  So, in this case, we just use a fresh name.*)
    lazymatch C with
      (argindex (let a := n in ?T) _) =>
      lazymatch (eval pattern C in f) with
        ?F _ =>
        let v := fresh a in
        constr:(fun (v : T) =>
                  ltac:(let b := (eval cbn beta in (F v)) in
                        let r := remove_argindexes (S n) b in
                        exact r))
      end
    end
  | context[argindex (let _ := n in _)] =>
    fail 1 "Something unexpectedly went wrong:" n f
  | context[argindex (let _ := _:nat in _)] =>
    (*in case of missing argindex numbers, due to specializing*)
    remove_argindexes (S n) f
  | context[argindex] =>
    fail 1 "Did you remember to use the abstractable prefix operator '#'?"
  | _ => f
  end.

Ltac label_args n T :=
  lazymatch T with
  | (forall (a : ?T), @?b a) =>
    constr:(forall (a : (let a:=n in T)),
               ltac:(let b' := eval cbn beta in (b a) in
                     let c:= label_args (S n) b' in exact c))
  | _ => T
  end.

Tactic Notation "abstracted" "as" ident(result) tactic3(tac) :=
  refine (let result := _ in _);
  let dummy :=
      constr:(
        ltac:(
          let Admit := fresh in
          intro Admit;
          let f := constr:(
                      ltac:(unshelve tac;
                            [apply (@argindex _ Admit)..])) in
          let r := remove_argindexes 1 f in
          let r' := eval cbn beta zeta in r in
          instantiate (1 := r') in (Value of result);
          exact I
        ): (forall T, T) -> True) in idtac.

(*Unfortunately, we have to clutter up the syntax even more with a first pass
over the function to be abstracted in order to label its args*)
Ltac abstractable f :=
  constr:(ltac:(let ft := type of f in
                let laft := label_args 1 ft in
                let F := fresh in
                pose (f : laft) as F;
                (*this appears fragile - various other combos collapse to ft
                in the result*)
                exact F)).

(*but we can minimize that clutter to a single prefix operator:*)
Notation "# f" := (ltac:(let f' := abstractable f in exact f')) (at level 0, only parsing).

(**********************************************************************)

Variable P : nat -> nat -> Type.
Variable Q : nat -> nat -> nat -> Type.
Variable R : Type.

Goal forall a b c, Q a b c -> (forall (x t y z : nat)(p : P x t)(q : Q x y z), R) -> True.
Proof.
  intros a b c H0 H.
  abstracted as H' eapply #H with (2 := H0).
  exact I.
Qed.

Goal forall a b, P a b -> (forall (x t y z : nat), P x t -> P y z -> Q x y z -> R) -> True.
Proof.
  intros a b H0 H.
  abstracted as H1 eapply #H with (1 := H0).
  abstracted as H2 eapply #H with (2 := H0).
  Fail abstracted as H3 eapply H with (1 := H0) (2 := H0).
  abstracted as H3 eapply #H with (1 := H0) (2 := H0).
  exact I.




(* Question.*)


Lemma test : (forall n:nat, n > 0 -> True) -> True.
intros H.

evar(P:Prop); assert P; [ subst P;

  let E := uconstr:(H _) in
  let F := uconstr:(E _) in
  refine F | ].




  simple refine F; shelve_unifiable | ].
admit.


unshelve eapply (H ltac:(evar (x:nat); exact x) _).


   (H _ _ E1 ?x ?P _ E2 ?y)


cbv zeta.


evar(P:Prop); assert P; [ subst P;
unshelve (eapply (H ltac:(evar (x:nat)) _))
|
].
admit.


unshelve (eapply (H ltac:(evar (x:nat)) _)).

unshelve eapply ltac:(evar (x:nat); assert (P:x>0); [ shelve | refine (H x P) ]).



eapply ltac:(eapply (H _)).

eapply ltac:(evar (x:nat); refine (H x)).

eapply ltac:(evar (x:nat); evar (P:x>0); refine (H x P)).

Unshelve.

Grab Existential Variables.

*)



(**************************************************************************
* Additional Tactics for Coq                                              *
* Distributed under the terms of the MIT license                          *
***************************************************************************)

(** Main features, at a glance:

  =>> I1 .. IN
    New intro pattern to name only non-dependent hypotheses.
    --> later will be part of SSR, as a variant of the "=>" tacticial.

  invert H
    Performs inversion, substitution (on fresh variables), clear,
    and re-generalize all fresh variables and hypotheses.

  #H E1 .. EN
    Syntax for terms to build applications on a first-match basis

  H E1 EN
  @H E1 EN
  #H E1 EN

  H _ EN

  H .. E1 .. EN



  forward I: H.

  H : forall .... -> ... -> G.


  set (I := H _ _ _ _);  clearbody I.

  assert (

 I: G


    --> currently only works for apply/put/forward
         applys (#H E1 .. EN).
         forward I: (#H E1 .. EN).
         put I: (#H E1 .. EN).
         rewrite (#H E1 EN)


Question: what should =>> do.
  def convergence: forall x y, exists.
  conv : convergence.
   =>>+.

  invert H. [ =>> M | =>> M N | ].



exact ltac:(let H := inst (H :: E1 .. :: EN)) in exact H)
*)




Set Implicit Arguments.
Require Import List.


(* ********************************************************************** *)
(** ** Tools for LibTac *)

(** A values of type [libtac_Dyn] consists of a pair of a type and
    a value of that type. This is useful for heterogenous lists.  *)

Inductive libtac_Dyn : Type :=
  | libtac_dyn : forall (A:Type), A -> libtac_Dyn.

(** [libtac_dyn_of E] returns a term of type [libtac_Dyn],
    according to the following rules:
    - if [E] is already of type [libtac_Dyn], then it returns [E];
    - otherwise, it returns the list [(libtac_dyn E)::nil]. *)

Ltac libtac_dyn_of E :=
  match type of E with
  | List.list libtac_Dyn => constr:(E)
  | _ => constr:((libtac_dyn E)::nil)
  end.

(** [libtac_wild], written [__] is used as a "wildcard argument"
    in LibTac tactics, which cannot reuse the simple wildcard [_]. *)

Inductive libtac_Wild : Set :=
  | libtac_wild : libtac_Wild.

Notation "'__'" := libtac_wild : libtac_scope.

Open Scope libtac_scope.

(** [libtac_Mark] and [libtac_mark] are dummy definitions used as sentinel
    by tactics, to mark a certain position in the context or in the goal. *)

Inductive libtac_Mark : Type :=
  | libtac_mark : libtac_Mark.

(** [libtac_gen_until_mark] repeats [generalize] on hypotheses from the
    context, starting from the bottom and stopping as soon as reaching
    an hypothesis of type [Mark].
    It fails if [Mark] does not appear in the context. *)

Ltac libtac_gen_until_mark :=
  match goal with H: ?T |- _ =>
  match T with
  | libtac_Mark => clear H
  | _ => generalize H; clear H; libtac_gen_until_mark
  end end.

(** [libtac_intro_until_mark] repeats [intro] until reaching an
    hypothesis of type [Mark]. It throws away the hypothesis [Mark].
    It fails if [Mark] does not appear as an hypothesis in the goal. *)

Ltac libtac_intro_until_mark :=
  match goal with
  | |- (libtac_Mark -> _) => intros _
  | _ => intro; libtac_intro_until_mark
  end.

(** [libtac_get_last_introduced_hyp] retreives the name of the
    last introduced hypothesis. This is useful for obtaining the
    "natural name" of the hypothesis. *)

Ltac libtac_get_last_introduced_hyp tt :=
  match goal with H: _ |- _ => constr:(H) end.

(** For implementing [invert], we use a tagging mechanism
    to keep track of which hypotheses will need to be
    generalized after the substitutions. We cannot simply
    rely on a mark in the context, because hypotheses may
    get shuffled during the substitution process. *)

Definition libtac_to_generalize (A:Type) (x:A) := x.

Ltac libtac_gen_to_generalize :=
  repeat match goal with
    H: libtac_to_generalize _ |- _ => generalize H; clear H end.

Ltac libtac_mark_to_generalize H :=
  let T := type of H in
  change T with (libtac_to_generalize T) in H.



(* ********************************************************************** *)
(** * Introduction in fast mode *)

(* [=>> I1 ... IN] is a variant of [intros I1 .. IN] where the
   patterns provided are only used to name non-dependent hypotheses.
   In other words, dependent variables are automatically introduced
   by this tactic. It stops just after introducing IN.

   [=>>] (without arguments) has a slightly different behavior:
   it introduces all the dependent variables at the head of the goal.
   In does nothing if there is no visible product at the head of the
   goal.

   This tactic fails if there is no non-dependent hypothesis at the
   head of the goal. *)


Ltac libtac_fast_intros_arg I :=
  hnf; match goal with
  | |- ?P -> ?Q => intros I
  | |- forall _, _ => intro; libtac_fast_intros_arg I
  end.

Ltac ltac_fast_intros_noarg_aux :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => intro; ltac_fast_intros_noarg_aux
  | |- _ => idtac
  end.

Ltac ltac_fast_intros_noarg := ltac_fast_intros_noarg_aux.

(* Use this alternative code to unfold head once
Ltac ltac_fast_intros_noarg :=
  match goal with
  | |- ?P -> ?Q => idtac
  | |- forall _, _ => ltac_fast_intros_noarg_aux
  | |- ?G => hnf;
       match goal with
       | |- ?P -> ?Q => idtac
       | |- forall _, _ => =>>_rec
       end
  | |- _ => idtac
  end.
*)

Tactic Notation "=>>" :=
  ltac_fast_intros_noarg.
Tactic Notation "=>>" simple_intropattern(I1) :=
  libtac_fast_intros_arg I1.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2) :=
  =>> I1; =>> I2.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) :=
  =>> I1; =>> I2 I3.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) :=
  =>> I1; =>> I2 I3 I4.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5) :=
  =>> I1; =>> I2 I3 I4 I5.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) :=
  =>> I1; =>> I2 I3 I4 I5 I6.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) :=
  =>> I1; =>> I2 I3 I4 I5 I6 I7.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8) :=
  =>> I1; =>> I2 I3 I4 I5 I6 I7 I8.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) :=
  =>> I1; =>> I2 I3 I4 I5 I6 I7 I8 I9.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) :=
  =>> I1; =>> I2 I3 I4 I5 I6 I7 I8 I9 I10.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) simple_intropattern(I11) :=
  =>> I1; =>> I2 I3 I4 I5 I6 I7 I8 I9 I10 I11.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) simple_intropattern(I11)
 simple_intropattern(I12) :=
  =>> I1; =>> I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I2.
Tactic Notation "=>>" simple_intropattern(I1) simple_intropattern(I2)
 simple_intropattern(I3) simple_intropattern(I4) simple_intropattern(I5)
 simple_intropattern(I6) simple_intropattern(I7) simple_intropattern(I8)
 simple_intropattern(I9) simple_intropattern(I10) simple_intropattern(I11)
 simple_intropattern(I12) :=
  =>> I1; =>> I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I2.


(* ********************************************************************** *)
(** * Inversion with substitution *)

(** The tactic [invert H] intends to replace [inversion H], bringing
    the following improvements:
    - the hypothesis [H] is cleared from the goal;
    - all generated equalities are substituted away immediately,
      (only the new equalities, not the ones that existed before);
    - all the fresh variables/hypotheses produced are placed
      in the goal, so that they can be named by the user.
*)

(** There are cases where the constructor of an inductive definition
    includes an equality that you would not like to be substituted
    during inversions. To prevent substitution, you may define this
    equality as [id (x = y)] instead of [x = y], or, alternatively,
    as [x =' y], where [='] is defined as follows:

      Definition eq' := @eq.
      Notation "x '='' y" := (@eq' _ x y)
         (at level 70, y at next level).
*)

(** The tactic [invert], in some cases, can be enhanced using the
    axiom of injectivity of dependent pairs.

    The injectivity of dependent pairs is a very standard axiom.
    It is a weak form of proof irrelevance.
    This axiom is useful to eliminate equalities of the form
    [existT P p x = existT P p y] produced by inversion, typically
    in the the case of inductive definitions with constructors
    of the form [ | Myconstructor: forall (T:Type), ...].
    If you do not like the axiom, simply replace the axiom with
    the line: [Definition inj_pair2 := True.]

    If you like to use the axiom from Coq stdlib instead, use:

     Require Eqdep.
     Lemma inj_pair2 :
       forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
       existT P p x = existT P p y -> x = y.
     Proof using. apply Eqdep.EqdepTheory.inj_pair2. Qed.
*)

Axiom inj_pair2 :
  forall (U : Type) (P : U -> Type) (p : U) (x y : P p),
  existT P p x = existT P p y -> x = y.

(** Implementation of the tactic *)

Ltac libtac_invert H :=
  let rec go tt :=
    match goal with
    | |- (libtac_Mark -> _) => intros _
    | |- (?x = ?y -> _) => let H := fresh "TEMP" in intro H;
                           first [ subst x | subst y ];
                           go tt
    | |- (existT ?P ?p ?x = existT ?P ?p ?y -> _) =>
         let H := fresh in intro H;
         generalize (@inj_pair2 _ P p x y H);
         clear H; go tt
    | |- (forall _, _) =>
       intro; let H := libtac_get_last_introduced_hyp tt in
       libtac_mark_to_generalize H; go tt
    end in
  pose libtac_mark;
  inversion H;
  clear H;
  generalize libtac_mark;
  libtac_gen_until_mark;
  go tt;
  libtac_gen_to_generalize;
  unfold libtac_to_generalize in *.

Tactic Notation "invert" hyp(H) :=
   libtac_invert H.

(** [invert_nosubst H] is similar to [invert H], except that it
    does not perform any substitution. *)

Tactic Notation "invert_nosubst" hyp(H) :=
   pose libtac_mark; inversion H; libtac_gen_until_mark; clear H.


(* ********************************************************************** *)
(** * First-match applications *)

(** DISCLAIMER: FOR TECHNICAL REASONS, THIS SYNTAX ONLY WORKS WHEN
    USED IN THE FOLLOWING TACTICS:
      [put I: (# E0 E1 .. EN)]
      [forward I: (# E0 E1 .. EN)]
      [applys (# E0 E1 .. EN)]
*)

(** The expression [# E0 E1 .. EN] is essentially equivalent to
    [E0 _ .. _ E1 _ .. .. _ EN] with the right number of underscores,
    as determined by a "first-match" greedy algorithm.

    In some cases, we have a term [E0] that expects two arguments of
    the same type, but we only want to specify the second argument.
    In this case, we can use the [__] place-holder, and write
    [#E0 __ E2].

    Another use of [__] is as last argument. [# E0 .. EN __] is the
    same as [(# E0 .. EN) _ _ .. _] with as many trailing underscores
    as there are visible produces in the type of the term [# E0 .. EN].
    This usage is useful for reasoning by forward chaining.

    Remark: there is one exception to the "first-match" principe:
    we purposely refuse to instantiate an argument of type "Type"
    with an expression that does not have the type "Type". Otherwise,
    the "Type" argument could get instantiated with a proposition,
    which is almost never the intention of the user.
*)

(* Implementation *)

Ltac libtac_app_assert t P cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ | cont(t H); clear H ].

Ltac libtac_app_evar t A cont :=
  let x := fresh "TEMP" in
  evar (x:A);
  let t' := constr:(t x) in
  let t'' := (eval unfold x in t') in
  subst x; cont t''.

Ltac libtac_app_arg t P v cont :=
  let H := fresh "TEMP" in
  assert (H : P); [ apply v | cont(t H); try clear H ].

Ltac libtac_app_typeclass t cont :=
  let t' := constr:(t _) in
  cont t'.

Ltac libtac_dynlist_next_type vs :=
  match vs with
  | nil => constr:(libtac_wild)
  | (libtac_dyn libtac_wild)::?vs' => libtac_dynlist_next_type vs'
  | (@libtac_dyn ?T _)::_ => constr:(T)
  end.

Ltac libtac_build_app_alls t final :=
  let rec go t :=
    match type of t with
    | ?P -> ?Q => libtac_app_assert t P go
    | forall _:?A, _ =>
        first [ libtac_app_evar t A go
              | libtac_app_typeclass t go
              | fail 3 ]
    | _ => final t
    end in
  go t.

Ltac ltac_first_match_app_cont_aux t vs final :=
  let rec go t vs :=
    match vs with
    | nil =>
        first [ final t | fail 1 ]
    | (libtac_dyn libtac_wild)::nil =>
        first [ libtac_build_app_alls t final | fail 1 ]
    | (libtac_dyn ?v)::?vs' =>
        let cont t' := go t' vs in
        let cont' t' := go t' vs' in
        let T := type of t in
        let T := eval hnf in T in
        match v with
        | libtac_wild =>
           first [ let U := libtac_dynlist_next_type vs' in
             match U with
             | libtac_wild =>
               match T with
               | ?P -> ?Q => first [ libtac_app_assert t P cont' | fail 3 ]
               | forall _:?A, _ => first [ libtac_app_typeclass t cont'
                                         | libtac_app_evar t A cont'
                                         | fail 3 ]
               end
             | _ =>
               match T with
               (* might be more efficient to test T for unifiability here *)
               | U -> ?Q => first [ libtac_app_assert t U cont' | fail 3 ]
               | forall _:U, _ => first
                   [ libtac_app_typeclass t cont'
                   | libtac_app_evar t U cont'
                   | fail 3 ]
               | ?P -> ?Q => first [ libtac_app_assert t P cont | fail 3 ]
               | forall _:?A, _ => first
                   [ libtac_app_typeclass t cont
                   | libtac_app_evar t A cont
                   | fail 3 ]
               end
             end
           | fail 2 ]
      | _ =>
          match T with
          | ?P -> ?Q => first [ libtac_app_arg t P v cont'
                              | libtac_app_assert t P cont
                              | fail 3 ]
          | forall _:Type, _ =>
              match type of v with
              | Type => first [ cont' (t v)
                              | libtac_app_evar t Type cont
                              | fail 3 ]
              | _ => first [ libtac_app_evar t Type cont
                           | fail 3 ]
              end
          | forall _:?A, _ =>
             let V := type of v in
             match type of V with
             | Prop => first [ libtac_app_typeclass t cont
                              | libtac_app_evar t A cont
                              | fail 3 ]
             | _ => first [ cont' (t v)
                          | libtac_app_typeclass t cont
                          | libtac_app_evar t A cont
                          | fail 3 ]
             end
          end
      end
    end in
  go t vs.

Ltac libtac_first_match_app_cont args final :=
  first [
    match args with (@libtac_dyn ?T ?t)::?vs =>
      let t := constr:(t:T) in
      ltac_first_match_app_cont_aux t vs final
      (*fast_rm_inside args*)
    end
  | fail 1 "Instantiation fails for:" args].

(* FOR FUTURE USE:
Ltac libtac_first_match_app args :=
  libtac_first_match_app_cont args ltac:(fun E => exact E).

FOR CURRENT WORK-AROUND: *)
Ltac libtac_first_match_app args := exact args.

(* Notation *)

Notation "'#'" :=
  (ltac:(libtac_first_match_app (@nil libtac_Dyn)))
  (at level 0, only parsing)
  : libtac_scope.
Notation "'#' v1" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::nil)))
  (at level 0, v1 at level 0)
  : libtac_scope.
Notation "'#' v1 v2" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, only parsing)
  : libtac_scope.
Notation "'#' v1 v2 v3" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0, only parsing)
  : libtac_scope.
Notation "'#' v1 v2 v3 v4" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, only parsing)
  : libtac_scope.
Notation "'#' v1 v2 v3 v4 v5" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, only parsing)
  : libtac_scope.
Notation "'#' v1 v2 v3 v4 v5 v6" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, only parsing)
  : libtac_scope.
Notation "'#' v1 v2 v3 v4 v5 v6 v7" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::(libtac_dyn v7)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0, only parsing)
  : libtac_scope.
Notation "'#' v1 v2 v3 v4 v5 v6 v7 v8" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::(libtac_dyn v7)::(libtac_dyn v8)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, only parsing)
  : libtac_scope.
Notation "'#' v1 v2 v3 v4 v5 v6 v7 v8 v9" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::(libtac_dyn v7)::(libtac_dyn v8)::(libtac_dyn v9)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, only parsing)
  : libtac_scope.
Notation "'#' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::(libtac_dyn v7)::(libtac_dyn v8)::(libtac_dyn v9)::(libtac_dyn v10)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, only parsing)
  : libtac_scope.
Notation "'#' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::(libtac_dyn v7)::(libtac_dyn v8)::(libtac_dyn v9)::(libtac_dyn v10)
   ::(libtac_dyn v11)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0, only parsing)
  : libtac_scope.
Notation "'#' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::(libtac_dyn v7)::(libtac_dyn v8)::(libtac_dyn v9)::(libtac_dyn v10)
   ::(libtac_dyn v11)::(libtac_dyn v12)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
   v12 at level 0, only parsing)
  : libtac_scope.


(* ********************************************************************** *)
(** * [put] tactic *)

(** [put I: E] is a convenient syntax for adding an hypothesis
    of name [I] and of proof-term [E] into the goal.

    Remark: [put I: E] is like [generalize E; intros I]
    or like [set (I:=E); clearbody I]. *)

Tactic Notation "put" simple_intropattern(I) ":" constr(E) :=
  (* FUTURE IMPLEMENTATION:  generalize E; intros I. *)
  let args := libtac_dyn_of E in
  libtac_first_match_app_cont args ltac:(fun R => generalize R; intros I).


(* ********************************************************************** *)
(** * [forward] tactic *)

(** [forward I: E] is essentially a convenient syntax for
    [put I: (# E __)], which instantiates all visible arguments
    from lemma [E] with fresh unification variables, and names
    [I] the instantiated lemma.
    *)

Tactic Notation "forward" simple_intropattern(I) ":" constr(E) :=
  (* FUTURE IMPLEMENTATION:  put I: (# E __). *)
  let args := libtac_dyn_of E in
  let args := (eval simpl in (args ++ ((libtac_dyn __)::nil))) in
  libtac_first_match_app_cont args ltac:(fun R => generalize R; intros I).


(* ********************************************************************** *)
(** * [applys] tactic *)

(** [applys E] is the same as [eapply E] except that it supports the
    [applys (# E0 .. EN)] form. FUTURE: it won't be needed anymore. *)

Tactic Notation "applys" constr(E) :=
  match type of E with
  | list libtac_Dyn => libtac_first_match_app_cont E ltac:(fun R => eapply R)
  | _ => eapply E
  end.




(**************************************************************************
* New Tactics for Coq -- Demos                                            *
* Distributed under the terms of the MIT license                          *
***************************************************************************)

Set Implicit Arguments.

(* Require Import LibTac.*)


(************************************************************************ *)
(** ** [dup] tactic for testing *)

(** [dup N] produces [N] copies of the current goal. It is useful
    for building examples on which to illustrate behaviour of tactics. *)

Lemma dup_lemma : forall P, P -> P -> P.
Proof using. auto. Admitted.

Ltac dup_tactic N :=
  match (*nat_from_number*) N with
  | 0 => idtac
  | S 0 => idtac
  | S ?N' => apply dup_lemma; [ | dup_tactic N' ]
  end.

Tactic Notation "dup" constr(N) :=
  dup_tactic N.



(* ********************************************************************** *)
(** * Fast introduction: [>>=] *)

Section IntroFastDemo.
Variables H1 H2 H3 H4 H5 H6 : Prop.
Variables P1 P2 P3 : nat -> Prop.

Lemma demo_intro_fast_1 :
  forall a b, P1 a -> P2 b -> forall c d, P3 c -> P1 d -> c = b.
Proof using.
  dup 4.
  (* [=>>] introduces all the variables which are not hypotheses,
     more precisely all the variables used dependently. *)
  - =>>.
  (* if there is no more head variables, and no definition can
     be unfolded at head of the goal, it does not do anything *)
    =>>. admit.
  (* [=>> A] introduces all variables, then does [intros A] *)
  - =>> A. =>> B. =>>. intros C D. admit.
  (* [=>>] may take several arguments, as illustrated below *)
  - =>> A B. =>>. admit.
  - =>> A B C D. admit.
Admitted.

Lemma demo_intro_fast_2 :
  forall a (c:nat) b, P1 a -> P2 b -> True.
Proof using.
  (* Notice that variables which are not used dependently
     are treated as hypotheses, e.g. variable [c] below. *)
  =>> c E F. admit.
Admitted.

Definition Same (x y : nat) := True -> x = y.
Definition Sym (x:nat) := forall y, x = y -> Same y x.

Lemma demo_intro_fast_3 :
  forall a, Sym a.
Proof using.
  dup 4.
  (* [=>>] introduces a variable but no subsequent definition *)
  - =>>. admit.
  (* [=>> E] unfolds definitions until finding an hypothesis *)
  - =>> E. =>> F. admit.
  (* [=>> E F] unfolds several definitions if needed *)
  - =>> E F. admit.
  (* [=>> ? _] shows that all intro pattern are accepted *)
  - =>> ? _. admit.
Admitted.

Lemma demo_intro_fast_4 :
  forall a, a = 0 -> Sym a.
Proof using.
  dup 5. (* more examples *)
  (* introduces [a] only *)
  - =>>. admit.
  (* introduces [a = 0] *)
  - =>> E. admit.
  (* introduces [a = 0] and [a = y] *)
  - =>> E F. admit.
  (* introduces [a = 0] and [a = y] and [True] *)
  - =>> E F G. admit.
  (* introduction of more names fails *)
  - try (=>> E F G H). admit.
Admitted.

Lemma demo_intro_fast_5 :
  forall a, a = 0 -> ~ Sym a.
Proof using.
  dup 2. (* playing with negation *)
  (* introduces [a = 0] *)
  - =>> E. admit.
  (* introduces [a = 0] and [Sym a] *)
  - =>> E F. admit.
Admitted.

End IntroFastDemo.



(* ********************************************************************** *)
(** * [invert] *)

(** The predicate [adds2 n m] asserts that [m=n+2]. *)

Inductive adds2 : nat -> nat -> Prop :=
  | adds2_0 : adds2 0 2
  | adds2_SS : forall n m, adds2 n m ->
              adds2 (S (S n)) (S (S m)).

Lemma demo_invert_1 :
  adds2 4 8 -> False.
Proof using.
  intros P. dup 4.
  (* [inversion] generates a lot of ugly stuff *)
  - inversion P. inversion H1. inversion H4.
  (* [inversion H; subst; clear H] is not ideal either *)
  - inversion P; subst; clear P.
   inversion H1; subst; clear H1.
   inversion H2; subst; clear H2.
  (* [invert] performs substitution only on new equalities,
     clears the hypothesis, and puts generated variables
     into the goals, to name them using [intros] or [=>>]. *)
  - invert P. =>> P1.
   invert P1; =>> P2.
   invert P2. (* proves the goal *)
  (* [invert] allows to reuse the same name *)
  - invert P; =>> P . invert P; =>> P. invert P.
Admitted.

(** The predicate [lt n m] asserts that [n<m]. *)

Inductive lt : nat -> nat -> Prop :=
  | lt_0 : forall n, lt 0 (S n)
  | lt_S : forall n m, lt n m -> lt (S n) (S m).

Lemma demo_invert_2 : forall a b,
  lt a b -> lt a (S b).
Proof using.
  =>> P. dup 3.
  (* When [invert] produces several subgoals, you can name
     the variables in each of the goals, when you reach to them. *)
  - invert P.
    + intros n. constructor.
    + intros n m R. constructor. admit.
  (* Alternatively, you can name variables immediately *)
  - invert P; [ intros n | intros n m R ].
    + constructor.
    + constructor. admit.
  (* This can be combined with the fast introduction syntax *)
  - invert P; [ =>> | =>> R ].
    + constructor.
    + constructor. admit.
Admitted.

(** The predicate [behave] relates a value of type nat and
    a value of type [behavior]. It is meant to illustrate
    an example where [inversion] produces a dependent equality. *)

Inductive behavior : Type :=
  | behavior_intro :
      forall (A:Type) (F:A->nat) (P:A->Prop), behavior.

Inductive behave : nat -> behavior -> Prop :=
  | behave_intro : forall (A:Type) (F:A->nat) (P:A->Prop) V,
      P V -> behave (F V) (@behavior_intro A F P).

Lemma demo_invert_3 :
  behave 4 (behavior_intro (fun x:nat => x) (fun x:nat => x <> 3))
  -> False.
Proof using.
  intros H. dup 2.
  (* [inversion] can generate some dependently-typed equalities *)
  - inversion H. admit.
  (* [inverts] carries out all the substitution properly *)
  - invert H. =>> R1 R2 R3. admit.
Admitted.


(* ********************************************************************** *)
(** ** [put] tactic *)

Section PutDemo.
Variables H1 H2 H3 H4 : Prop.

Lemma demo_put :
  (H1 -> H2 -> H3 /\ H4) -> (H1 -> H2) -> H1 -> H3.
Proof using.
  intros P Q R.
  (* [put] a tactic for naming a term *)
  put U: (Q R).
  (* [put] can decompose terms with a patterns *)
  put [V W]: (P R U).
  (* [put] accepts any intro-pattern in fact *)
  put (V'&_): (P R U).
  (* [put] can be used in particular to copy an hypothesis,
     for example if you need to save it before an [invert]. *)
  put U': U.
  admit.
Admitted.

End PutDemo.


(* ********************************************************************** *)
(** ** First-match application: [#] *)

(* See the documentation of [#] and [put] in the file LibTac.v. *)

Lemma demo_put_forward_sharp : forall (x y : nat) (A B : Prop),
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
  =>> Pos Neq Iff L M. dup 15.
  (* Specializes the lemma [M] to the hypothesis [Pos], skipping [n] *)
  - put P: (#M Pos). admit.
  (* Specializes the lemma [M] to the hypothesis [Iff], skipping [n,Pos,P,Q] *)
  - put P2: (#M Pos Iff). admit.
  (* Specializes even further dosnw *)
  - put P: (#M Neq). eauto. eauto. admit.
  (* Specializes only on [n] *)
  - put P: (#M x). admit.
  (* Specializes only on [m], which has the same type as [n], using [__] *)
  - put P: (#M __ y). eauto. eauto. admit.
  (* Specializes only on [m], and argument after it *)
  - put P: (#M __ y Neq). eauto. eauto. admit.
  (* Similarly, specializes only on [B], which has the same type as [A] *)
  - put P: (#M x __ B). eauto. admit.
  (* Using an introduction pattern to open an existential *)
  - put (k&K): (#L Neq). eauto. admit.
  (* Using a trailing [__] to instantiate all that remains *)
  - put [k K]: (#L Pos __). eauto. admit.
  (* More extreme instantiation *)
  - put R: (#L __). eauto. eauto. admit.
  (* Alternative syntax using [forward] *)
  - forward R: L. eauto. eauto. admit.
  (* Refined versions using [forward] *)
  - forward (k&K): (#L x y). eauto. eauto. admit.
Admitted.

Lemma demo_forward_1 : forall x : nat, x > 1 ->
  (forall z, z > 1 -> exists y, z < 2 /\ z <> y) ->
  True.
Proof using.
  =>> Le H. dup 2.
  (* [forward] is used to instantiate a lemma entirely, generating one
     subgoal for each hypothesis and one existential variable for
     each universally quantified variable *)
  - forward Q: H. eauto. admit.
  (* an introduction-pattern can be used to decompose the result *)
  - forward [y [R1 R2]]: H. eauto. admit.
Admitted.

Lemma demo_forward_2 :
  (forall x y : nat, x = y -> x <= y) ->
  forall a b : nat, a <= a.
Proof using.
  intros. forward K: (#H __ a). reflexivity. apply K.
Admitted.

(** Similar demos, showing how head definitions are unfolded *)

Definition mydef := forall (n m : nat), n = m -> False.

Lemma demo_forward_3 :
  forall (i:nat), mydef -> i <> i.
Proof using.
  =>> H. dup 3.
  (** forward does nothing if no quantifier is visible *)
  - forward I: H. admit.
  (** work-around is to force underscore *)
  - forward I: (#H __). apply (refl_equal i). admit.
  (** or to force one arguments *)
  - forward I: (H i). reflexivity. admit.
Admitted.

(** On the other hand, definitions that are not at head
    position are not unfolded *)

Definition outerdef := mydef.
Definition nesteddef := forall (n:nat), mydef.

Lemma demo_forward_4 :
  forall (i:nat), nesteddef -> outerdef.
Proof using.
  intros i H. dup 5.
  (** forwards does not instantiate [mydef] from [H] *)
  - forward K: (#H i). admit.
  (** it is nevertheless possible to instantiate arguments
      inside [mydef] if providing explicit arguments *)
  - forward K: (#H i i). admit. admit.
  (* or by adding a [__] *)
  - forward K: (#H i __). admit. admit.
  (* illustrating the interest of several [__] *)
  - forward K: (#H __ __). exact i. apply (refl_equal 0). admit.
  (** but usually it is simpler to unfold explicitly *)
  - unfold nesteddef, mydef in H.
    forward K: (#H i). apply (refl_equal 0). admit.
Admitted.

Lemma demo_applys : forall (x y : nat) (A B : Prop),
  (x > 0) ->
  (x <> y) ->
  (A <-> B) ->
  (forall n : nat,
   n > 0 ->
   forall P Q : Prop,
   (P <-> Q) ->
   forall m : nat,
   m <> n ->
   True) ->
  True.
Proof using.
  =>> Pos Neq Iff M. dup 5.
  (* [applys] is used to apply an instantiated lemma. *)
  - applys (#M Pos). eauto. eauto.
  - applys (#M A B). eauto. eauto. eauto.
  - applys (#M Pos Iff). eauto.
  - applys (#M Iff). eauto. eauto.
  - applys (#M x Iff). eauto. eauto.
Admitted.





(**************************************************************************
* New Tactics for Coq                                                     *
* Distributed under the terms of the MIT license                          *
***************************************************************************)


Set Implicit Arguments.
Require Import List.


(* ********************************************************************** *)
(** ** Tools for LibTac *)

(** A values of type [libtac_Dyn] consists of a pair of a type and
    a value of that type. This is useful for heterogenous lists.  *)

Inductive libtac_Dyn : Type :=
  | libtac_dyn : forall (A:Type), A -> libtac_Dyn.

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

(** The expression [$ E0 E1 .. EN] is essentially equivalent to
    [E0 _ .. _ E1 _ .. .. _ EN] with the right number of underscores,
    as determined by a "first-match" greedy algorithm.

    In some cases, we have a term [E0] that expects two arguments of 
    the same type, but we only want to specify the second argument.
    In this case, we can use the [__] place-holder, and write 
    [$E0 __ E2].

    Another use of [__] is as last argument. [$ E0 .. EN __] is the
    same as [($ E0 .. EN) _ _ .. _] with as many trailing underscores
    as there are visible produces in the type of the term [$ E0 .. EN].
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

Ltac ltac_build_app_alls t final :=
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
        first [ ltac_build_app_alls t final | fail 1 ]
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

Ltac libtac_first_match_app args :=
  libtac_first_match_app_cont args ltac:(fun E => exact E).

(* Notation *)

Notation "'$'" :=
  (ltac:(libtac_first_match_app (@nil libtac_Dyn)))
  (at level 0, only parsing)
  : libtac_scope.
Notation "'$' v1" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::nil)))
  (at level 0, v1 at level 0)
  : libtac_scope.
Notation "'$' v1 v2" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, only parsing)
  : libtac_scope.
Notation "'$' v1 v2 v3" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0, only parsing)
  : libtac_scope.
Notation "'$' v1 v2 v3 v4" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, only parsing)
  : libtac_scope.
Notation "'$' v1 v2 v3 v4 v5" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, only parsing)
  : libtac_scope.
Notation "'$' v1 v2 v3 v4 v5 v6" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, only parsing)
  : libtac_scope.
Notation "'$' v1 v2 v3 v4 v5 v6 v7" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::(libtac_dyn v7)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0, only parsing)
  : libtac_scope.
Notation "'$' v1 v2 v3 v4 v5 v6 v7 v8" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::(libtac_dyn v7)::(libtac_dyn v8)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, only parsing)
  : libtac_scope.
Notation "'$' v1 v2 v3 v4 v5 v6 v7 v8 v9" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::(libtac_dyn v7)::(libtac_dyn v8)::(libtac_dyn v9)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, only parsing)
  : libtac_scope.
Notation "'$' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::(libtac_dyn v7)::(libtac_dyn v8)::(libtac_dyn v9)::(libtac_dyn v10)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, only parsing)
  : libtac_scope.
Notation "'$' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::(libtac_dyn v7)::(libtac_dyn v8)::(libtac_dyn v9)::(libtac_dyn v10)
   ::(libtac_dyn v11)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0, only parsing)
  : libtac_scope.
Notation "'$' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12" :=
  (ltac:(libtac_first_match_app ((libtac_dyn v1)::(libtac_dyn v2)::(libtac_dyn v3)::(libtac_dyn v4)::(libtac_dyn v5)
   ::(libtac_dyn v6)::(libtac_dyn v7)::(libtac_dyn v8)::(libtac_dyn v9)::(libtac_dyn v10)
   ::(libtac_dyn v11)::(libtac_dyn v12)::nil)))
  (at level 0, v1 at level 0, v2 at level 0, v3 at level 0,
   v4 at level 0, v5 at level 0, v6 at level 0, v7 at level 0,
   v8 at level 0, v9 at level 0, v10 at level 0, v11 at level 0,
   v12 at level 0, only parsing)
  : libtac_scope.


(* ********************************************************************** *)
(** * Put tactic *)

(** [put I: E] is a convenient syntax for adding an hypothesis 
    of name [I] and of proof-term [E] into the goal.

    Remark: [put I: E] is like [generalize E; intros I] 
    or like [set (I:=E); clearbody I]. *)

Tactic Notation "put" simple_intropattern(I) ":" constr(E) :=
  generalize E; intros I.


(* ********************************************************************** *)
(** * Forward tactic *)

(** [forward I: E] is essentially a convenient syntax for 
    [put I: ($ E __)], which instantiates all visible arguments 
    from lemma [E] with fresh unification variables, and names 
    [I] the instantiated lemma. 
    *) 

Tactic Notation "forward" simple_intropattern(I) ":" constr(E) :=
  put I: ($ E __).
























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
(** ** First-match application: [$] *)

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
  =>> Pos Neq Iff L M.
  (* [lets] is used to instantiate a lemma [M] on arguments *)

  lets P: M Iff. eauto. clear P.
  lets P: (>> M Neq). eauto. eauto. clear P.
  lets P: (>> M __ y). eauto. eauto. clear P.
  lets P: (>> M x __ B). eauto. instantiate (1:=A) in P. clear P.
  (* [Hnts] keyword can be omitted *)
  lets P: (>> M __ y Neq). eauto. eauto. clear P.
  (* The syntax [>>] is not required for less than 5 arguments. *)
  lets P: M Pos A B Neq. eauto. clear P.
  (* A triple underscore indicates to instantiate all remaining *)
  lets k K: (>> L Pos ___). eauto. clears k.
  lets k K: (>> L ___). eauto. eauto. clears k.
  (* [forwards I: (>> E E1 .. EN)] is short for
     [lets I: (>> E E1 .. EN ___)] *)
  forwards R: L. eauto. eauto. clear R.
  forwards R: L Pos. eauto. clear R.
  forwards k K: L. eauto. eauto. clears k.
  forwards [k K]: L Pos y. eauto. clears k.
  forwards k K: (>> L x y). eauto. eauto. clears k.
  lets k K: (>> L Neq). eauto. clears k.
  auto.
Admitted.


Lemma demo_forwards_1 : forall x : nat, x > 1 ->
  (forall z, z > 1 -> exists y, z < 2 /\ z <> y) -> 
  True.
Proof using.
  =>> Le H. dup 4.
  (* [forwards] is used to instantiate a lemma entirely, generating one
     subgoal for each hypothesis and one existential variable for 
     each universally quantified variable *)
  forwards Q: H. eauto. admit. 
  (* an introduction-pattern can be used to decompose the result *)
  forwards [y [R1 R2]]: H. eauto. admit. 
  (* and [forwards] can also be used without introduction pattern *)
  forwards: H. eauto. admit. 
  (* [forwards] does nothing on an hypothesis without quantifiers *)
  forwards: Le. admit. 
Admitted.

Lemma demo_forwards_2 : 
  (forall x y : nat, x = y -> x <= y) ->
  forall a b : nat, a <= a.
Proof using.
  intros. dup 2. (* some more examples *)
    forwards K: (H a). reflexivity. apply K.
    forwards* K: (H a).
Admitted.

Lemma demo_applys_specializes : forall (x y : nat) (A B : Prop),
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
  =>> Pos Neq Iff M. dup 17.
  (* [applys] is used to apply an instantiated lemma. *)
  applys (>> M Pos). eauto. eauto.
  applys (>> M A B). eauto. eauto. eauto.
  applys (>> M Pos Iff). eauto.
  applys (>> M Iff). eauto. eauto.
  applys (>> M x Iff). eauto. eauto.
  applys M x Iff. eauto. eauto.
  (* [specializes] is used to instantiate an hypothesis in-place *)
  specializes M (>> 3). auto. 
  specializes M (>> 3 A B). auto. auto.
  specializes M (>> A __ __). eauto. eauto. auto.
  specializes M (>> Pos Iff 2). eauto. auto.
  (* A triple underscore indicates to instantiate all remaining *)
  specializes M (>> Pos ___). eauto. eauto. auto.
  specializes M (>> __ B ___). eauto. eauto. eauto. auto.
  specializes M __. specializes M __. eauto. auto.
  (* [specializes] can be used as [forwards in] thanks to [___] *)
  specializes M ___. eauto. eauto. eauto. auto.
  (* In those tactics, one can apply the constant [rm] to any subterm
     to request the argument of [rm] to be removed from the context. *)
  applys (>> M (rm Pos) Iff). (* [Pos] is gone here *) eauto.
  (* In fact, [rm] can be applied in depth inside terms *)
  specializes M (>> (proj1 (conj (rm Pos) Neq))). (* [Pos] is gone *) auto. 
Admitted.

(** Similar demos, showing how head definitions are unfolded *)

Definition mydef := forall (n m : nat), n = m -> False.

Lemma demo_specializes_definition :
  forall (i:nat), mydef -> i <> i.
Proof using.
  =>> H. dup 6. 
  (** specializes one by one *)
  specializes H i. specializes H i.
   specializes H (refl_equal i). false.
  (** specializes all arguments *)
  specializes H i i (refl_equal i). false.
  (** specializes admitping some arguments *)
  specializes H (refl_equal i). false.
  (** forwards all arguments *)
  forwards: H. apply (refl_equal i). false.
  (** forwards on one arguments *)
  forwards M: H i. reflexivity. false.
  (** build using lets *)
  lets: (>> H (refl_equal i)). false.
Admitted. 

(** Unfolding occurs recursively *)

Definition outerdef := mydef.

Lemma demo_specializes_definition_2 : 
  forall (i:nat), outerdef -> i <> i.
Proof using.
  =>> H. dup 6.
  (** specializes one by one *)
  specializes H i. specializes H i.
   specializes H (refl_equal i). false.
  (** specializes all arguments *)
  specializes H i i (refl_equal i). false.
  (** specializes admitping some arguments *)
  specializes H (refl_equal i). false.
  (** forwards all arguments *)
  forwards: H. apply (refl_equal i). false.
  (** forwards on one arguments *)
  forwards M: H i. reflexivity. false.
  (** build using lets *)
  lets: (>> H (refl_equal i)). false.
Admitted. 

(** On the other hand, definitions that are not at head
    position are not unfolded *)

Definition nesteddef := forall (n:nat), mydef.

Lemma demo_specializes_definition_3 : 
  forall (i:nat), nesteddef -> outerdef.
Proof using.
  intros i H. dup 4.
  (** forwards does not instantiate [mydef] from [H] *)
  forwards K: H i. admit. 
  (** ... unless explicitely visible *)
  unfold nesteddef, mydef in H.
   forwards K: H i. apply (refl_equal i). false.
  (** yet, it should be possible to instantiate arguments
      inside [mydef] if providing explicit arguments *)
  lets K: (>> H i i). admit. 
  lets K: (>> H i (refl_equal i)). admit. 
Admitted.


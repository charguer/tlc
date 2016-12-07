(* TEMPORARY *)

(*

(*-----------*)
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

  introv Pos Neq Iff L M.
Require Import List.
  build_app (((boxer M)::(boxer Iff)::nil)) ltac:(fun R => generalize R).
  build_app (((boxer M)::(boxer Iff)::nil)) ltac:(fun R => lets_base Fr R).



  build_app ((boxer M)::(boxer Iff)::nil) ltac:(fun Fr => set (L:=Fr)).

  lets_build Fr  ((boxer M)::(boxer Iff)::nil).

  build_app args ltac:(fun R => lets_base I R).


  let Ei := constr:(>> M Iff) in lets_build Fr Ei.
  lets I: Ei.

Ltac lets_build I Ei :=




 lets_build I ((boxer M)::(boxer Iff)::nil).
  let args := list_boxer_of Ei in
  let args := args_unfold_head_if_not_product_but_params args in
(*    let Ei''' := args_unfold_head_if_not_product Ei'' in*)
  build_app args ltac:(fun R => lets_base I R).



  build_app ((boxer M)::(boxer Iff)::nil) ltac:(fun E => pose E).


Ltac  :=
  first [
    match args with (@boxer ?T ?t)::?vs =>
      let t := constr:(t:T) in
      build_app_hnts t vs final;
      fast_rm_inside args
    end
  | fail 1 "Instantiation fails for:" args].



  build_app_hnts M ((boxer Iff)::nil) ltac:(fun E => pose E).

  lets P: (>> M Iff). eauto. clear P.

  build_app_hnts M ((boxer Iff)::nil) ltac:(fun E => pose E).



*)


(**************************************************************************
* New Tactics for Coq -- Demos                                            *
* Distributed under the terms of the MIT license                          *
***************************************************************************)

Set Implicit Arguments.
Require Import LibTac.


(**************************************************************************
(** ** [dup] tactic for testing *)

(** [dup N] produces [N] copies of the current goal. It is useful
    for building examples on which to illustrate behaviour of tactics. *)

Lemma dup_lemma : forall P, P -> P -> P.
Proof using. auto. Qed.

Ltac dup_tactic N :=
  match nat_from_number N with
  | 0 => idtac
  | S 0 => idtac
  | S ?N' => apply dup_lemma; [ | dup_tactic N' ]
  end.

Tactic Notation "dup" constr(N) :=
  dup_tactic N.



(* ********************************************************************** *)
(** * Fast introduction: [>>=] *)

Section IntrovTest.

Variables P1 P2 P3 : nat -> Prop.

Lemma demo_introv_1 :
  forall a b, P1 a -> P2 b -> forall c d, P3 c -> P1 d -> c = b.
Proof using.
  dup 4.
  (* [introv] introduces all the variables which are not hypotheses,
     more precisely all the variables used dependently. *)
  introv.
  (* if there is no more head variables, and no definition can
     be unfolded at head of the goal, it does not do anything *)
  introv. skip.
  (* [introv A] introduces all variables, then does [intros A] *)
  introv A. introv B. introv. intros C D. skip.
  (* [introv] may take several arguments, as illustrated below *)
  introv A B. introv. skip.
  introv A B C D. skip.
Qed.


Definition Same (x y : nat) := True -> x = y.
Definition Sym (x:nat) := forall y, x = y -> Same y x.

Lemma demo_introv_2 :
  forall a, Sym a.
Proof using.
  dup 4.
  (* [introv] introduces a variable but no subsequent definition *)
  introv.
  (* [introv] unfolds definition if no variable is visible *)
  introv. skip.
  (* [introv E] unfolds definitions until finding an hypothesis *)
  introv E. introv F. skip.
  (* [introv E F] unfolds several definitions if needed *)
  introv E F. skip.
  (* [introv] may unfold definition without any introduction *)
  introv E. introv. skip.
Qed.

Lemma demo_introv_3 :
  forall a, a = 0 -> Sym a.
Proof using.
  dup 5. (* more examples *)
  (* introduces [a] only *)
  introv. skip.
  (* introduces [a = 0] *)
  introv E. skip.
  (* introduces [a = 0] and [a = y] *)
  introv E F. skip.
  (* introduces [a = 0] and [a = y] and [True] *)
  introv E F G. skip.
  (* introduction of more names fails *)
  try (introv E F G H). skip.
Qed.

Definition TestSym := (forall a, a = 0 -> Sym a).

Lemma demo_introv_4 :
  TestSym.
Proof using.
  dup 2. (* same as before, except the goal itself is a definition *)
  (* introduces [a] only *)
  introv. skip.
  (* introduces [a = 0] *)
  introv E. skip.
Qed.

Lemma demo_introv_5 :
  forall a, a = 0 -> ~ Sym a.
Proof using.
  dup 2. (* playing with negation *)
  (* introduces [a = 0] *)
  introv E. skip.
  (* introduces [a = 0] and [Sym a] *)
  introv E F. skip.
Qed.

(* Iterated unfolding to get hypotheses *)

Definition AllSameAs (x:nat) := forall y, Same y x.
Definition AllSame := forall x, AllSameAs x.

Lemma demo_introv_6 :
  AllSame.
Proof using.
  dup 2.
  (* introduces only [x], then only [y] *)
  introv. introv. skip.
  (* introduces [x] and [y] and [True] *)
  introv E. skip.
Qed.

Definition AllSameAgain := AllSame.

Lemma demo_introv_7 :
  AllSameAgain.
Proof using.
  dup 2.
  (* introduces only [x], then only [y] *)
  introv. introv. skip.
  (* introduces [x] and [y] and [True] *)
  introv E. skip.
Qed.

Lemma demo_introv_8 :
  forall a (c:nat) b, P1 a -> P2 b -> True.
Proof using.
  (* notice that variables which are not used dependently
     are treated as hypotheses, e.g. variable [c] below.
     This might not be the desired behaviour, but that's
     all I'm able to implement in Ltac. *)
  introv c E F. skip.
Qed.

Definition IMP P A (x y : A) := P -> x = y.

Lemma demo_intros_all :
     (forall a b, P1 a -> P2 b -> IMP H1 a b)
  /\ (forall a b, a = 0 -> b = 1 -> ~ (a = b)).
Proof using.
  split.
  (* [intros_all] introduces as many arguments as possible *)
  intros_all. skip.
  intros_all. skip.
Qed.

(* An example showing that [intro] is not very-well
   specified with respect to beta-reduction, explaining
   why [introv] isn't doing better. *)

Definition testing f :=
  forall (x:nat), f x -> True.

Lemma demo_introv_what_to_do : testing (fun a => a = 0).
Proof using.
  dup 2.
    intro. skip. (* does beta-reduce f *)
    hnf. intro. skip. (* does not beta-reduce f *)
Qed.

End IntrovTest.



(* ********************************************************************** *)
(** * [invert] *)

Inductive even_shift : nat -> nat -> Prop :=
  | even_0 : even_shift 0 2
  | even_SS : forall n m, even_shift n m ->
              even_shift (S (S n)) (S (S m)).

Lemma demo_invert :
  even_shift 4 8 -> False.
Proof using.
  intros P. dup 12.
  (* [inversion] generates a lot of ugly stuff *)
  inversion P. inversion H7. inversion H10.
  (* [inversions H] is short for [inversion H; subst; clear H] *)
  inversions P. inversions H7. inversions H8.
  (* [invert] is same as [inversion H; clear H] except that it
     generalizes the generated hypotheses so that they can
     be named manually using intros or introv *)
  invert P. introv P' EQ1 EQ2. skip.
  (* [invert as] can be used to name the generated hypotheses
     directly, in the [introv] fashion *)
  invert P as P' EQ1 EQ2. skip.
  (* [inverts] does the same as [inversion; clear], then it
     substitutes all the generated equalities (and only
     these fresh equalities, not the older ones) *)
  inverts P. inverts H7. inverts H8.
  (* it is /sometimes/ possible to name the resulting hypotheses *)
  inverts P as P'. inverts P' as P''. inverts P''.
  (* it is even possible to reuse the same name *)
  inverts P as P. inverts P as P. inverts P.
  (* [invert as] without arguments leaves the hypotheses
     that have been generated in the goal *)
  inverts P as. introv P'. skip.
  (* one may add the keyword [keep] in order to keep the
     inverted hypothesis *)
  invert keep P. intros. skip.
  inverts keep P as P' EQ1 EQ2. skip.
  inverts keep P as. introv P'. skip.
  (* [lets_inverts] need to be used to invert expressions
     that are not simply the name of an hypothesis *)
  lets_inverts (conj P P) as H1 H2. skip.
Qed.

(* TODO: false_invert *)

Inductive Behave : Type :=
  | Behave_intro :
      forall (A:Type) (F:A->nat) (P:A->Prop), Behave.

Inductive behave : nat -> Behave -> Prop :=
  | behave_intro : forall (A:Type) (F:A->nat) (P:A->Prop) V,
      P V -> behave (F V) (@Behave_intro A F P).

Lemma demo_dependent_invert :
  behave 4 (Behave_intro (fun x:nat => x) (fun x:nat => x <> 3))
  -> False.
Proof using.
  intros H. dup 3.
  (* [inversion] can generate some dependently-typed equalities *)
  inversion H. (* look at H9 and H10 *) skip.
  (* [inverts] carries out all the substitution properly *)
  inverts H. skip.
  (* again, it is possible to name the new hypotheses *)
  inverts H as R1 R2 R3. skip.
Qed.

Lemma demo_inject_and_injects : forall a b c,
  (a,b,c) = (1,2,3) -> b = 2.
Proof using.
  introv EQ. dup 5.
  (* [injection] generates some equalities in the goal *)
  injection EQ. skip.
  (* [inject] does the same *)
  inject EQ. skip.
  (* but it is also able to name these hypotheses *)
  inject EQ as EQ1 EQ2 EQ3. skip.
  (* and [injects] can substitute these hypotheses *)
  injects EQ. skip.
  (* it also works if the equalities are in the other direction *)
  symmetry in EQ. injects EQ. skip.
Qed.


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
  introv Pos Neq Iff L M.
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
Qed.


Lemma demo_forwards_1 : forall x : nat, x > 1 ->
  (forall z, z > 1 -> exists y, z < 2 /\ z <> y) ->
  True.
Proof using.
  introv Le H. dup 4.
  (* [forwards] is used to instantiate a lemma entirely, generating one
     subgoal for each hypothesis and one existential variable for
     each universally quantified variable *)
  forwards Q: H. eauto. skip.
  (* an introduction-pattern can be used to decompose the result *)
  forwards [y [R1 R2]]: H. eauto. skip.
  (* and [forwards] can also be used without introduction pattern *)
  forwards: H. eauto. skip.
  (* [forwards] does nothing on an hypothesis without quantifiers *)
  forwards: Le. skip.
Qed.

Lemma demo_forwards_2 :
  (forall x y : nat, x = y -> x <= y) ->
  forall a b : nat, a <= a.
Proof using.
  intros. dup 2. (* some more examples *)
    forwards K: (H a). reflexivity. apply K.
    forwards* K: (H a).
Qed.

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
  introv Pos Neq Iff M. dup 17.
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
Qed.

(** Similar demos, showing how head definitions are unfolded *)

Definition mydef := forall (n m : nat), n = m -> False.

Lemma demo_specializes_definition :
  forall (i:nat), mydef -> i <> i.
Proof using.
  introv H. dup 6.
  (** specializes one by one *)
  specializes H i. specializes H i.
   specializes H (refl_equal i). false.
  (** specializes all arguments *)
  specializes H i i (refl_equal i). false.
  (** specializes skipping some arguments *)
  specializes H (refl_equal i). false.
  (** forwards all arguments *)
  forwards: H. apply (refl_equal i). false.
  (** forwards on one arguments *)
  forwards M: H i. reflexivity. false.
  (** build using lets *)
  lets: (>> H (refl_equal i)). false.
Qed.

(** Unfolding occurs recursively *)

Definition outerdef := mydef.

Lemma demo_specializes_definition_2 :
  forall (i:nat), outerdef -> i <> i.
Proof using.
  introv H. dup 6.
  (** specializes one by one *)
  specializes H i. specializes H i.
   specializes H (refl_equal i). false.
  (** specializes all arguments *)
  specializes H i i (refl_equal i). false.
  (** specializes skipping some arguments *)
  specializes H (refl_equal i). false.
  (** forwards all arguments *)
  forwards: H. apply (refl_equal i). false.
  (** forwards on one arguments *)
  forwards M: H i. reflexivity. false.
  (** build using lets *)
  lets: (>> H (refl_equal i)). false.
Qed.

(** On the other hand, definitions that are not at head
    position are not unfolded *)

Definition nesteddef := forall (n:nat), mydef.

Lemma demo_specializes_definition_3 :
  forall (i:nat), nesteddef -> outerdef.
Proof using.
  intros i H. dup 4.
  (** forwards does not instantiate [mydef] from [H] *)
  forwards K: H i. skip.
  (** ... unless explicitely visible *)
  unfold nesteddef, mydef in H.
   forwards K: H i. apply (refl_equal i). false.
  (** yet, it should be possible to instantiate arguments
      inside [mydef] if providing explicit arguments *)
  lets K: (>> H i i). skip.
  lets K: (>> H i (refl_equal i)). skip.
Qed.


*)
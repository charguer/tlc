(**************************************************************************
* Useful General-Purpose Tactics for Coq - Demo scripts                   *
* Arthur Chargueraud                                                      *
* Distributed under the terms of the LGPL-v3 license                      *
***************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics.
Require Import Coq.micromega.Lia.


(* ********************************************************************** *)
(** ** Demo of [check] *)

(* Uncomment to use

Lemma demo_check : True.
Proof using.
  (* sucessful check *)
  check (1 = 2).
  (* unsucessful check *)
  Fail check (1 = true).
  (* disable check *)
  Ltac check_enabled ::= constr:(false).
  (* do nothing *)
  check (1 = true).
  (* restore default mode *)
  Ltac check_enabled ::= constr:(true).
Abort.

*)

(* ********************************************************************** *)
(** ** Definitions used in demos *)

Parameter H1 H2 H3 H4 H5 H6 : Prop.


(* ********************************************************************** *)
(** ** Assertions, cuts, contradiction *)

Lemma demo_false_1 :
  forall (n:nat), (forall m, m = n -> False) -> H1.
Proof using.
  intros n P. dup 5.
  (* [false_goal] replaces the current goal by [False] *)
  { false. eapply P. reflexivity. }
  (* [false E] proves the goal if [E] has type [False] *)
  { false (P n (refl_equal n)). }
  (* [false E] is in fact the same as [false; apply E] *)
  { false P. reflexivity. }
  (* [false*] is short for [false; eauto] *)
  { false*. }
  (* [false] also tries and call [congruence] *)
  { lets: (P n). false. }
Qed.

Lemma demo_false_2 :
  0 = 1 -> 1 = 2.
Proof using.
  intros. dup 3.
  (* [contradiction] does not cover [discriminate] *)
  try contradiction. demo.
  discriminate.
  (* while [false] covers [contradiction] and [discriminate] *)
  false.
Qed.

Lemma demo_false_3 :
  (forall b, b = false) -> False.
Proof using.
  introv H. dup.
  (* [false E] is able to use [forwards E] to exhibit
     a contradiction. *)
  false (>> H true).
  (* syntax [false E1 .. EN] is also available *)
  false H true.
Qed.

Lemma demo_tryfalse :
  forall n, S n = 1 -> n = 0.
Proof using.
  intros. dup 2.
  (* often in a case analysis, several subcases are absurd. example: *)
  destruct n. auto. false.
  (* [tryfalse] removes all the subcases solved by [false] *)
  destruct n; tryfalse. auto.
Qed.

Lemma demo_asserts_cuts :
  True.
Proof using.
  dup 7.
  (* here is another syntax for assert *)
  asserts U: H2. demo. demo.
  (* that allows for intro-patterns *)
  asserts [U V]: (H2 /\ H3). demo. demo.
  (* the intro-pattern [U [V W]] may be simply written U V W *)
  asserts U V W: (H2 /\ H3 /\ H4). demo. demo.
  (* this is also convenient for existentials *)
  asserts x y E F: (exists x y, S x = y /\ x > 0). demo. demo.
  (* if no pattern is provided, a fresh name is generated *)
  asserts: (H2 /\ H3). demo. demo.
  (* [asserts~] calls [auto] only on the asserted proposition. *)
  asserts~ U: (0 = 0). demo.
  (* [cuts] is like [asserts] except it swaps subgoals *)
  cuts U V: (H2 /\ H3). demo. demo.
Qed.


(* ********************************************************************** *)
(** ** Assumptions *)

Lemma demo_lets :
  (H1 -> H2 -> H3 /\ H4) -> (H1 -> H2) -> H1 -> H3.
Proof using.
  intros P Q R.
  (* [lets] is a tactic for naming a term *)
  lets U: (Q R).
  (* [lets] can decompose terms with a patterns *)
  lets [V W]: (P R U).
  (* again, the syntax for conjunctions applies *)
  lets V1 W1: (P R U).
  (* [lets] without an intro-pattern generates a fresh name *)
  lets: (P R).
  (* [lets] on an existing hypothesis makes a copy of it *)
  lets U': U.
  demo.
Qed.


(* ********************************************************************** *)
(** * Apply *)

Definition Dup x := x + x.

Lemma demo_applys : forall P : (nat -> nat) -> nat -> Prop,
  (forall f, P f (f 0)) -> P Dup 0.
Proof using.
  intros. dup 4.
  (* while apply is able to do some unification *)
  apply (H Dup).
  (* since CoqV8.2, apply is able to do this unfolding *)
  apply H.
  (* before, one had to use [refine] *)
  refine (H _).
  (* [applys H] is simply [refine (H _ ... _)] with enough many underscores *)
  applys H.
Qed.

Lemma demo_applys_to :
  (H1 -> H2 -> H3 /\ H4) -> (H1 -> H2) -> H1 -> H3.
Proof using.
  introv P Q R. dup.
  (* [applys_to R] is used to apply a lemma to [R] and name R the result *)
  applys_to R Q. demo.
  (* another example *)
  applys_to R P. demo.
Qed.


(* ********************************************************************** *)
(** * Introduction *)

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
  introv. demo.
  (* [introv A] introduces all variables, then does [intros A] *)
  introv A. introv B. introv. intros C D. demo.
  (* [introv] may take several arguments, as illustrated below *)
  introv A B. introv. demo.
  introv A B C D. demo.
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
  introv. demo.
  (* [introv E] unfolds definitions until finding an hypothesis *)
  introv E. introv F. demo.
  (* [introv E F] unfolds several definitions if needed *)
  introv E F. demo.
  (* [introv] may unfold definition without any introduction *)
  introv E. introv. demo.
Qed.

Lemma demo_introv_3 :
  forall a, a = 0 -> Sym a.
Proof using.
  dup 5. (* more examples *)
  (* introduces [a] only *)
  introv. demo.
  (* introduces [a = 0] *)
  introv E. demo.
  (* introduces [a = 0] and [a = y] *)
  introv E F. demo.
  (* introduces [a = 0] and [a = y] and [True] *)
  introv E F G. demo.
  (* introduction of more names fails *)
  try (introv E F G H). demo.
Qed.

Definition TestSym := (forall a, a = 0 -> Sym a).

Lemma demo_introv_4 :
  TestSym.
Proof using.
  dup 2. (* same as before, except the goal itself is a definition *)
  (* introduces [a] only *)
  introv. demo.
  (* introduces [a = 0] *)
  introv E. demo.
Qed.

Lemma demo_introv_5 :
  forall a, a = 0 -> ~ Sym a.
Proof using.
  dup 2. (* playing with negation *)
  (* introduces [a = 0] *)
  introv E. demo.
  (* introduces [a = 0] and [Sym a] *)
  introv E F. demo.
Qed.

(* Iterated unfolding to get hypotheses *)

Definition AllSameAs (x:nat) := forall y, Same y x.
Definition AllSame := forall x, AllSameAs x.

Lemma demo_introv_6 :
  AllSame.
Proof using.
  dup 2.
  (* introduces only [x], then only [y] *)
  introv. introv. demo.
  (* introduces [x] and [y] and [True] *)
  introv E. demo.
Qed.

Definition AllSameAgain := AllSame.

Lemma demo_introv_7 :
  AllSameAgain.
Proof using.
  dup 2.
  (* introduces only [x], then only [y] *)
  introv. introv. demo.
  (* introduces [x] and [y] and [True] *)
  introv E. demo.
Qed.

Lemma demo_introv_8 :
  forall a (c:nat) b, P1 a -> P2 b -> True.
Proof using.
  (* notice that variables which are not used dependently
     are treated as hypotheses, e.g. variable [c] below.
     This might not be the desired behaviour, but that's
     all I'm able to implement in Ltac. *)
  introv c E F. demo.
Qed.

Definition IMP P A (x y : A) := P -> x = y.

Lemma demo_intros_all :
     (forall a b, P1 a -> P2 b -> IMP H1 a b)
  /\ (forall a b, a = 0 -> b = 1 -> ~ (a = b)).
Proof using.
  split.
  (* [intros_all] introduces as many arguments as possible *)
  intros_all. demo.
  intros_all. demo.
Qed.

(* An example showing that [intro] is not very-well
   specified with respect to beta-reduction, explaining
   why [introv] isn't doing better. *)

Definition testing f :=
  forall (x:nat), f x -> True.

Lemma demo_introv_what_to_do : testing (fun a => a = 0).
Proof using.
  dup.
    intro. demo. (* does beta-reduce f *)
    hnf. intro. demo. (* does not beta-reduce f *)
Qed.

End IntrovTest.

(*------------------------*)
(** * Arrow Introduction  *)

Section ArrowTest.

Parameters P1 P2 P3 : nat -> Prop.

Lemma demo_arrow_1 :
  forall a b, P1 a -> P2 b -> forall c d, P3 c -> P1 d -> c = b.
Proof using.
  dup 4.
  (* [=>>] introduces all the variables which are not hypotheses,
     more precisely all the variables used dependently. *)
  =>>.
  (* if there is no more head variables, and no definition can
     be unfolded at head of the goal, it does not do anything *)
  =>>. demo.
  (* [=>> A] introduces all variables, then does [intros A] *)
  =>> A. =>> B. =>>. =>> C D. demo.
  (* [=>>] may take several arguments, as illustrated below *)
  =>> A B. =>>. demo.
  =>> A B. =>>. =>> C D. demo.
Qed.

Lemma demo_arrow_2 :
  forall a, Sym a.
Proof using.
  dup 4.
  (* [=>>] introduces a variable but no subsequent definition *)
  =>>.
  (* [=>>] unfolds definition if no variable is visible *)
  =>>. demo.
  (* [=>> E] unfolds definitions until finding an hypothesis *)
  =>> E. =>> F. demo.
  (* [=>> E ? F] unfolds several definitions if needed *)
  =>> E ? F. demo.
  (* [=>>] may unfold definition without any introduction *)
  =>> x E. =>>. demo.
Qed.

Lemma demo_arrow_3 :
  forall (a:nat), a = 0%nat -> Sym a.
Proof using.
  dup 5. (* more examples *)
  (* introduces [a] only *)
  =>>. demo.
  (* introduces [a = 0] *)
  =>> E. demo.
  (* introduces [a = 0] and [a = y] *)
  =>> E; =>> F. demo.
  (* introduces [a = 0] and [a = y] and [True] *)
  =>> E; =>> F G. demo.
  (* introduction of more names fails *)
  try (=>> E; =>> F G H). demo.
Qed.

Lemma demo_arrow_4 :
  TestSym.
Proof using.
  dup 2. (* same as before, except the goal itself is a definition *)
  (* introduces [a] only *)
  =>>. demo.
  (* introduces [a = 0] *)
  =>> E. demo.
Qed.

Lemma demo_arrow_5 :
  forall a:nat, a = 0%nat -> ~ Sym a.
Proof using.
  dup 2. (* playing with negation *)
  (* introduces [a = 0] *)
  =>> E. demo.
  (* introduces [a = 0] and [Sym a] *)
  =>> E F. demo.
Qed.

Lemma demo_arrow_6 :
  AllSame.
Proof using.
  dup 2.
  (* introduces only [x], then only [y] *)
  =>>. =>>. demo.
  (* introduces [x] and [y] and [True] *)
  =>> ? E. demo.
Qed.

Lemma demo_arrow_7 :
  AllSameAgain.
Proof using.
  dup 2.
  (* introduces only [x], then only [y] *)
  =>>. =>>. demo.
  (* introduces [x] and [y] and [True] *)
  =>> ? E. demo.
Qed.

End ArrowTest.


(* ********************************************************************** *)
(** * Generalization, naming *)

Lemma demo_gen_and_generalizes :
  forall P Q : nat -> nat -> nat -> Prop,
  forall a b c, P a b c -> Q a a a -> P b b c -> True.
Proof using.
  intros. dup 3.
  (* [gen] generalizes an hypothesis and clears it *)
  gen H. demo.
  (* it generalizes all the dependencies of a variable *)
  gen a. demo.
  (* it also works for several variables at once *)
  gen b c. demo.
Qed.

Inductive ind : nat -> Prop :=
  | ind_0 : ind 0
  | ind_S : forall n, ind n -> ind (S n)
  | ind_SS : forall n, ind n -> ind (S (S n))
  | ind_P : forall (A:Type) (P:A->Prop) (f:A->nat) (a:A),
       ind (f a) -> P a -> ind (S (f a)).

Lemma demo_sets_and_set_eq_and_sets_eq : forall n,
  ind (3 + n) -> ind (7 + n) -> ind (7 + n).
Proof using.
  introv M1 M2. dup 9.
  (* [sets] introduces a name and performs the substitution *)
  sets a: (3+n). demo.
  sets b: (7+n). demo.
  (* [set_eq] introduces an equality *)
  set_eq a Ha: (7+n). demo.
  (* [sets_eq] introduces an equality and substitutes *)
  sets_eq a Ha: (7+n). demo.
  (* the name of the hypothesis can be generated *)
  sets_eq a: (7+n). demo.
  (* the name of the variable can also be generated *)
  sets_eq: (7+n). demo.
  (* [set_eq in H] performs the substitution in [H] *)
  set_eq a: (7+n) in M2. demo.
  (* [set_eq in |-] performs no substitution *)
  set_eq a: (7+n) in |-. demo.
  (* [set_eq <-] generates the equality [7+n=a] *)
  sets_eq <- a: (7+n). demo.
Qed.

Lemma demo_sets_let_and_sets_eq_let : forall n1 n2 : nat,
  (let x := n1 + n2 in x = x) ->
  (let y := n2 + n1 in let z := y + y in z = z) ->
  (let t := n1 + n1 in t = t).
Proof using.
  intros n1 n2 M1 M2. dup 3.
  (* [sets_let x] introduces a local definition for a let;
     note that, due to a limitation of Coq, only one local
     binding can be named! *)
  sets_let a. sets_let b. sets_let c. auto.
  (* the hypothesis where to look can be specified *)
  sets_let a in M1. auto.
  (* [sets_eq_let] introduces explicit equalities like [sets_eq] *)
  sets_eq_let a. sets_eq_let b. sets_eq_let c. auto.
Qed.


(* ********************************************************************** *)
(** * Evars *)

Lemma demo_check_noevar_goal : forall (n:nat),
  (forall m, m = n -> True) -> True.
Proof using.
  intros. check_noevar_goal. eapply H.
  try check_noevar_goal. dup.
  reflexivity. check_noevar_goal. auto.
Qed.


(* ********************************************************************** *)
(** * Unfolding *)

Definition Id A (x:A) := x.

Lemma demo_unfolds_folds :
  forall a b, a = Id(b) -> Dup a = 0 -> Dup b = Id(0+0).
Proof using.
  intros. dup 2.
  (* [unfolds] is same as [unfold in *] *)
  unfolds Dup. demo.
  (* [unfolds] can take several arguments *)
  unfolds Id,Dup.
  subst b.
  (* [folds] is same as [fold in *]. *)
  folds (Dup a). demo.
Qed.

Definition Twice (P:Prop) := True -> P /\ P.

Lemma demo_unfolds_head_definition :
  forall P:Prop, (True -> P) -> Twice P -> Twice P.
Proof using.
  introv A B.
  (* [unfolds] without arguments unfolds the head definition *)
  unfolds.
  (* it also applies to an hypothesis *)
  unfolds in B.
  demo.
Qed.


(* ********************************************************************** *)
(** * Simplification *)

Lemma demo_simpls_and_unsimpl :
  forall a b, Dup a = (1+1) -> Dup b = Id(0+0).
Proof using.
  intros.
  (* [simpls] is same as [simpl in *] *)
  simpls.
  (* [unsimpl] can be used to undo a simplification *)
  unsimpl (0+0).
  unsimpl (2+0) in H.
  demo.
Qed.


(* ********************************************************************** *)
(** * Substitution *)

(* DEPRECATED: [subst] tactic has been fixed

Lemma demo_substs_1 : forall a b c d e : nat,
  a = b -> b = c -> d = e -> e = d -> P1 d -> P2 a -> P3 c.
Proof using.
  introv P Q R U V. dup 2.
  (* [subst] does not work with circular equalities *)
  try subst. demo.
  (* [substs] does work however *)
  substs. demo.
Qed.

Lemma demo_substs_2 : forall x y (f:nat->nat),
  x = f x -> y = x -> y = f x.
Proof using.
  intros.
  (* [subst] does not work *)
subst.
  try subst.
  (* [substs] does work *)
  substs.
  assumption.
Qed.

*)


Lemma subst_hyp_demo : forall (x y x' y' z z' : nat) (P:nat->Prop),
  (x,y,z) = (x',y',z') ->
  P x -> P x' -> P y -> P y' -> P z -> P z' ->
  z = z'.
Proof using.
  introv H. intros.
  subst_hyp_base H. auto.
Qed.



(* ********************************************************************** *)
(** * Rewriting *)

Lemma demo_rewrites :
  (forall n m, m + n = n + m) -> 3 + 4 = 7.
Proof using.
  introv H. dup.
  (* [rewrites] support the [rm] identity tag to remove hypothesis *)
  rewrites (rm H). demo.
  (* [rewrites] can take arguments like [forwards] -- see further *)
  rewrites (>> H __ 3). demo.
Qed.

Lemma demo_rewrites_at : forall x y z,
  x = y + y -> x + x = z -> z + z = x + x + x + x.
Proof using.
  introv E H. dup.
  (* [rewrite] rewrites in all similar occurences *)
  rewrite E. demo.
  (* [rewrites at] can be used to control the target of rewrite *)
  rewrites E at 2.
  rewrites E at 2 in H.
  rewrites <- H at 2.
  demo.
Qed.

Lemma demo_rewrite_all :
  (forall n, n + 0 = 0 + n) ->
  (3 + 0) + 0 = 5 + 0.
Proof using.
  intros E.
  (* [rewrite_all] is same as [repeat rewrite] *)
  rewrite_all E. demo.
Qed.

Lemma demo_asserts_and_cuts_rewrite : forall n,
  0 < n < 2 -> P1 1 -> P1 n.
Proof using.
  introv Lt H. dup 2.
  (* [asserts_rewrite] rewrites and generates a proof obligation *)
  asserts_rewrite (n = 1). demo. demo.
  (* same for [cuts_rewrite], except the subgoals are swapped *)
  cuts_rewrite (n = 1). demo. demo.
Qed.

Lemma demo_replaces : forall a b, a = b + b -> a + a + a = 3 * a.
Proof using.
  intros. dup 3.
  (* [replaces] replaces all occurences (the equality subgoal is first) *)
  replaces a with 3. demo. demo.
  (* [replaces at] replaces at a given occurence *)
  replaces a at 2 with 5. demo. demo.
  (* [replaces] and [replaces at] works in hypotheses *)
  replaces b at 2 with 4 in H. demo. demo.
Qed.

Lemma demo_pi_rewrite : forall (P:Prop) (X:P->nat) (p1 p2:P),
   X p1 + X p2 = X p2 + X p1.
Proof using.
  (* [pi_rewrite E] replaces any proposition [E] with an evar
     of the same type. This is very useful when working with
     terms that are unifiable modulo proof irrelevance *)
  intros. pi_rewrite p1. reflexivity.
Qed.



(* ********************************************************************** *)
(** * Inversions *)

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
  invert P. introv P' EQ1 EQ2. demo.
  (* [invert as] can be used to name the generated hypotheses
     directly, in the [introv] fashion *)
  invert P as P' EQ1 EQ2. demo.
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
  inverts P as. introv P'. demo.
  (* one may add the keyword [keep] in order to keep the
     inverted hypothesis *)
  invert keep P. intros. demo.
  inverts keep P as P' EQ1 EQ2. demo.
  inverts keep P as. introv P'. demo.
  (* [lets_inverts] need to be used to invert expressions
     that are not simply the name of an hypothesis *)
  lets_inverts (conj P P) as H1 H2. demo.
Qed.

(* --TODO: false_invert *)

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
  inversion H. (* look at H9 and H10 *) demo.
  (* [inverts] carries out all the substitution properly *)
  inverts H. demo.
  (* again, it is possible to name the new hypotheses *)
  inverts H as R1 R2 R3. demo.
Qed.

Lemma demo_inject_and_injects : forall a b c,
  (a,b,c) = (1,2,3) -> b = 2.
Proof using.
  introv EQ. dup 5.
  (* [injection] generates some equalities in the goal *)
  injection EQ. demo.
  (* [inject] does the same *)
  inject EQ. demo.
  (* but it is also able to name these hypotheses *)
  inject EQ as EQ1 EQ2 EQ3. demo.
  (* and [injects] can substitute these hypotheses *)
  injects EQ. demo.
  (* it also works if the equalities are in the other direction *)
  symmetry in EQ. injects EQ. demo.
Qed.


(* ********************************************************************** *)
(** * Case_if *)

Lemma demo_case_if : forall b c :bool,
  (if b then true else true) = false ->
  (if c then true else true) = true.
Proof using.
  intros. dup 4.
  case_if. auto. auto.
  case_if as P. auto. auto.
  case_if in H.
  case_if in H as P.
Qed.

(* ********************************************************************** *)
(** * F_equal *)

Lemma demo_fequals_1 : forall a b c d,
  b = d -> d = 2 -> a = 1 ->
  (a,b,c) = (1,2,3).
Proof using.
  intros. dup 3.
  (* [f_equal] is not really clever on tuples *)
  f_equal. f_equal. demo. demo. demo.
  (* while [fequal] works better *)
  fequal. demo. demo. demo.
  (* even more useful, [fequals] tries to discharge the easy
     subgoals using [reflexivity] and [congruence] *)
  fequals. demo.
Qed.

Lemma demo_fequals_2 : forall f a b c d,
  b = d -> d = 2 -> a = 1 ->
  f a b c = f 1 2 3 :> nat.
Proof using.
  intros. dup 2.
  (* [fequal] and [fequals] also work for functions, of course *)
  fequal. demo. demo. demo.
  fequals. demo.
Qed.

(** [fequals] supports proof irrelevance *)

Lemma demo_fequal_post :
  forall (P:Prop) (X:P->nat) (p1 p2:P), X p1 = X p2.
Proof using. intros. fequals. Qed.


(* ********************************************************************** *)
(** * Induction *)

Inductive natequal : nat -> nat -> Prop :=
  | natequal_O : natequal 0 0
  | natequal_S : forall n, natequal n n -> natequal (S n) (S n).

(* --TODO

Lemma demo_inductions : forall n m p,
  natequal (n + m) (m + p) -> p = n.
Proof using.
  intros. dup.
  (* [induction] does not work -- too weak hypotheses *)
  induction H. demo. demo.
  (* but [inductions], based on [dependent induction], does work. *)
  inductions H gen n m p. demo. demo.
Qed.

Lemma demo_inductions' : forall n m,
  natequal (n + m) 0 -> n = 0.
Proof using.
  intros. dup.
  (* same *)
  induction H. demo. demo.
  (* correct version *)
  inductions H gen n m. demo.
Qed.

*)

(* ********************************************************************** *)
(** ** N-ary splitting and branching *)

Definition test_split_1 := H1 /\ H2 /\ H3.
Definition test_split_2 := H4 /\ H5 /\ H6 /\ test_split_1.
Definition test_split_3 := test_split_2.

Lemma demo_splits : test_split_3.
Proof using.
  dup 4.
  (* spliting a bunch of conjunction is a pain *)
  split. demo. split. demo. split. demo. split. demo. demo.
  (* but it is sometimes too aggressive. *)
  (* [splits N] splits a conjunction in N parts *)
  splits 4. demo. demo. demo. demo.
  splits 3. demo. demo. demo.
  (* [splits] is able to guess the appropriate arity *)
  splits. demo. demo. demo. splits. demo. demo. demo.
Qed.

Lemma demo_branch :
  1 = 2 \/ 2 = 3 \/ 3 = 4 \/ 4 = 4 \/ 4 = 5 \/ 5 = 6.
Proof using.
  dup 6.
  (* [branch K of N] is used to select a branch of a disjunction *)
  branch 1 of 6. demo.
  branch 4 of 6. auto.
  branch 6 of 6. demo.
  (* [branch] can usually guess the appopriate arity *)
  branch 1. demo.
  branch 4. auto.
  branch 6. demo.
Qed.

Lemma demo_destructs :
  1 = 2 /\ (2 = 3 /\ 3 = 4) /\ 4 = 5 -> True.
Proof using.
  intros H. destructs H. demo.
Qed.


(* ********************************************************************** *)
(** * Hide, clears, sorts *)

Parameter lemma_hide : forall n, n + 0 = n.

Lemma demo_hide_hyps : forall x:nat, x + 0 = x.
Proof using.
  intros.
  (* Any term has the type [Something] *)
  generalize (lemma_hide : Something). intros H.
  generalize (lemma_hide : Something). intros H'.
  (* [show_hyp H] unfolds the definition of [Something] *)
  show_hyp H.
  (* [hide_hyp H] reveals the definition of [Something] *)
  hide_hyp H.
  (* [show_hyps] and [hide_hyps] apply to all hypotheses of sort Prop *)
  show_hyps.
  hide_hyps.
  (* Hidden terms remain convertible with their original value *)
  hnf in H.
  apply H'.
Qed.

Lemma demo_hide_def : forall x:nat,
   let y := x + x in let z := y in y + 0 = y.
Proof using.
  intros.
  (* [hide_def x] hides the body of a definition *)
  hide_def y.
  hide_def z.
  (* [show_def x] reveals the body of a definition *)
  show_def y.
  show_def z.
  (* [hide_defs] and [show_defs] applies to all definitions *)
  hide_defs.
  show_defs.
  (* [show_def] can be used to unfold [Something] in the goal *)
  hide_def y.
  unfold y.
  show_def.
  demo.
Qed.

Lemma demo_hide_generic : forall x:nat,
   let y := x + x + x + x in let z := y in y + 0 = y.
Proof using.
(* NEWCOQ_BUG
  intros.
  generalize (lemma_hide). intros H.
  (* [hide]/[show] work both for definition and hypotheses *)
  hide H.
  hide y.
  show H.
  show y.
  (* [hide_all]/[show_all] hide everything *)
  hide_all.
  show_all.
  (* Observe that substitution of hidden terms may require
     several unfolding. *)
  hide_all. subst y. show_def z. show_def z.
  (* The tactic [show_all] reveals everything at once *)
  show_all.
  hide_all.
  apply H.
*)
demo.
Qed.

Lemma demo_hide_term : forall x,
  x + x + x = 3.
Proof using.
  intros.
  (* using [hide_term E] and [show_term] *)
  hide_term (x+x+x).
  show_term.
  (* typically used in a pattern matching *)
  match goal with |- ?T = _ => hide_term T end.
  demo.
Qed.

Lemma demo_clears : forall (x y z : nat) (A B : Prop),
  (x > 0) ->
  (x <> y) ->
  (A <-> B) ->
  True.
Proof using.
  introv z Pos Neq Iff. dup 5.
  (* [clears] is like [clear] except it clears all dependencies *)
  clears y. demo.
  clears x. demo.
  clears x y. demo.
  clears Neq A. demo.
  (* [clears] without arguments clears only unused variables
     (which are not propositions) *)
  clears. demo.
Qed.

Lemma demo_sort :
  forall n : nat,
  n > 0 ->
  forall P Q : Prop,
  (P <-> Q) ->
  forall m : nat,
  m <> n ->
  forall K : nat -> Prop,
  K n ->
  forall p,
  K (m+p) ->
  True.
Proof using.
  intros.
  (* [sort] puts all the proposition at the bottom of the context *)
  sort. demo.
Qed.


(* ********************************************************************** *)
(** * Admit *)

Lemma demo_admit : forall n m p : nat,
  n > m -> m >= p -> n > p.
Proof using.
  intros. dup 6.
  (* [admits H: E] is used to accept a new fact *)
  admits R1: (m = m). demo.
  admits (R1&R2): (m = m /\ n > m+1). demo.
  admits (q&Q): (exists q, q > p). demo.
  admits: (m <> n). demo.
  (* [admit_rewrite E] is used to accept a fact E and rewrite it *)
  admit_rewrite (m = n) in H0. demo.
  (* [admit_goal] is used to do an induction and cheat on the
     induction hypothesis, by having it as strong as the initial goal *)
  dup.
    induction p. demo. demo.
    admit_goal IH. destruct p. demo. demo.
Qed.


(* ********************************************************************** *)
(** ** Advanced instantiation *)

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
  forwards Q: H. eauto. demo.
  (* an introduction-pattern can be used to decompose the result *)
  forwards [y [R1 R2]]: H. eauto. demo.
  (* and [forwards] can also be used without introduction pattern *)
  forwards: H. eauto. demo.
  (* [forwards] does nothing on an hypothesis without quantifiers *)
  forwards: Le. demo.
Qed.

Lemma demo_forwards_2 :
  (forall x y : nat, x = y -> x <= y) ->
  forall a b : nat, a <= a.
Proof using.
  intros. dup. (* some more examples *)
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
  forwards K: H i. demo.
  (** ... unless explicitely visible *)
  unfold nesteddef, mydef in H.
   forwards K: H i. apply (refl_equal i). false.
  (** yet, it should be possible to instantiate arguments
      inside [mydef] if providing explicit arguments *)
  lets K: (>> H i i). demo.
  lets K: (>> H i (refl_equal i)). demo.
Qed.


(* ********************************************************************** *)
(** ** [equates]: introduction of equalities to enable [apply] to work *)

Lemma demo_ereplace_working : forall (P:nat->nat->Prop) x y,
  (forall n, P n n) -> (x > 0 -> x = y) -> (x > 0) -> P x y.
Proof using.
  introv H E L. dup 4.
  (* here, the hypothesis [P n n] cannot be applied directly *)
  try apply H.
  (* however, we really want to be able to apply it *)
  eapply equates_2. apply H. auto.
  (* this is particularly useful for automation *)
  eapply equates_2; eauto.
  (* the tactic [equates] inputs the position where
     evars should be introduced in place of arguments;
     the indices are to be counted from the right. *)
  equates 2. demo. demo.
Abort.

Lemma demo_equates_non_dep : forall (P:nat->nat->nat->Prop) x y z,
  P x y z.
Proof using.
  intros. dup 6.
  equates 1. demo. demo.
  equates 2. demo. demo.
  equates 3. demo. demo.
  (* multiple [equates] are allowed *)
  equates 1 2. demo. demo. demo.
  equates (>> 1 2). demo. demo. demo.
Abort.

Lemma demo_equates_dep : forall (P:nat->forall A, A->Prop) x (T:Type) z,
  P x T z.
Proof using.
  intros. dup 4.
  equates 1. demo. demo.
  (* replacement of dependent hypotheses is not allowed *)
  try equates 2.
  equates 3. demo. demo.
  equates 1 3. demo. demo. demo.
Abort.


(* ********************************************************************** *)
(** ** [applys_eq]: application of lemma up to equality *)

Lemma demo_applys_eq : forall (P:nat->nat->nat->Prop) x x' y y' z z',
     (P x y z -> P x y z')
  /\ (P x y z -> P x' y z)
  /\ (P x y z -> P x' y' z)
  /\ (P x y z -> P x' y' z').
Proof using.
  intros. splits; intros M.
  { applys_eq_core M. demo. }
  { applys_eq_core M. demo. }
  { applys_eq_core M. demo. demo. }
  { applys_eq_core M. demo. demo. demo. }
Abort.

Lemma demo_applys_eq_dep : forall (P:forall A, A->nat->Prop) T x x' y y',
     (P T x y-> P T x y')
  /\ (P T x y -> P T x' y)
  /\ (P T x y -> P T x' y').
Proof using.
  intros. splits; intros M.
  { applys_eq_core M. demo. }
  { applys_eq_core M. demo. }
  { applys_eq_core M. demo. demo. }
Abort.

Lemma demo_applys_eq_dep_middle : forall (P:nat->forall A, A->Prop) x x' (T:Type) y y',
     (P x T y -> P x T y')
  /\ (P x T y -> P x' T y)
  /\ (P x T y -> P x' T y').
Proof using.
  intros. splits; intros M.
  { applys_eq_core M. demo. }
  { applys_eq_core M. demo. }
  { applys_eq_core M. demo. demo. }
Abort.


(* ********************************************************************** *)
(** ** Induction on height of a derivation *)

Section IndHeight.

(** Lambda calculus *)

Inductive trm : Type :=
  | trm_var : nat -> trm
  | trm_abs : nat -> trm -> trm
  | trm_app : trm -> trm -> trm.

Parameter subst : nat -> trm -> trm -> trm.

(** Original big-step reduction judgment *)

Inductive bigred : trm -> trm -> Prop :=
  | bigred_val : forall v,
      bigred v v
  | bigred_abs : forall x t,
      bigred (trm_abs x t) (trm_abs x t)
  | bigred_app : forall t1 t2 x t3 v2 v,
      bigred t1 (trm_abs x t3) ->
      bigred t2 v2 ->
      bigred (subst x v2 t3) v ->
      bigred (trm_app t1 t2) v.

(** Same judgment, with an index to bound the height *)

Inductive bigredh : nat -> trm -> trm -> Prop :=
  | bigredh_val : forall n v,
      bigredh (S n) v v
  | bigredh_abs : forall n x t,
      bigredh (S n) (trm_abs x t) (trm_abs x t)
  | bigredh_app : forall n t1 t2 x t3 v2 v,
      bigredh n t1 (trm_abs x t3) ->
      bigredh n t2 v2 ->
      bigredh n (subst x v2 t3) v ->
      bigredh (S n) (trm_app t1 t2) v.

Hint Extern 1 ((_ < _)%nat) => lia.

Hint Constructors bigred bigredh.

Lemma bigredh_lt : forall n n' t v,
  bigredh n t v -> (n < n')%nat -> bigredh n' t v.
Proof using.
  introv H. gen n'. induction H; introv L;
   (destruct n' as [|n']; [ false; lia | autos* ]).
Qed.

Lemma bigredh_bigred : forall n t v, (* optional *)
  bigredh n t v -> bigred t v.
Proof using. introv H. induction* H. Qed.

Lemma bigred_bigredh : forall t v,
  bigred t v -> exists n, bigredh n t v.
Proof using. hint bigredh_lt. introv H. induction H; try induct_height. Qed.

(** After exploiting this last lemma, it is possible to perform an
    induction on the height of a derivation by doing [induction n]. *)

End IndHeight.



(* ********************************************************************** *)
(** ** Notation for exists *)

Lemma demo_exist_1 :
  exists x1 x2 x3, x1 = x2 /\ x2 = x3 /\ x3 = 0.
Proof using.
  (* dup N makes N copies of the current goal, which is useful for demos *)
  dup 6.
  (* N-ary existentials are displayed in a packed way,
     and they can be instantiated at once *)
  exists 0 0 0. auto.
  (* [exists~ 0 0 0] is the same as [exists 0 0 0] followed with auto *)
  exists~ 0 0 0.
  (* if a wild-card is provided, an existential variable is introduced *)
  exists __ 0 __. demo.
  (* if a double wild-card is provided, as many existential as possible
     are introduced *)
  exists 0 ___.
  (* [exists] without arguments is the same as [exists __ ... __],
     for the number of visible existentials in the goal (with hnf. *)
  exists. demo.
Abort.

Lemma demo_exists_2 :
     (exists n, n = 0)
  /\ (exists n m, n = m /\ n = 0)
  /\ (exists n, def_with_exists n)
  /\ (0 = 0).
Proof using.
  splits.
  { exists. admit. }
  { exists. admit. }
  { exists. admit. }
  { try exists. (* failure expected *) admit. }
Abort.


(* ********************************************************************** *)
(** ** ['let]-binding *)

Definition demo_let_binding_test_1 :
  ('let x := 3 in 'let y := x + x in y + y) = 12.
Proof using.
  dup 3.
  (* One can compute with ['let] *)
  reflexivity.
  (* One can inline ['let] step by step *)
  simpl. (* does nothing *)
  let_simpl.
  let_simpl.
  reflexivity.
  (* One can name the arguments of ['let] step by step *)
  let_name. (* --TODO: avoid naming of x in 12 *)
  let_name as z.
  subst x. subst z. reflexivity.
Qed.

Definition demo_let_binding_test_2 :
  ('let x := 3 in 'let y := x + x in y + y) = 12 -> True.
Proof using.
  dup 2; intros H.
  (* One can inline ['let] step by step *)
  simpl in H. (* does nothing *)
  let_simpl in H.
  let_simpl in H.
  auto.
  (* One can name the arguments of ['let] step by step *)
  let_name in H.
  let_name in H as z.
  subst x. subst z. auto.
Qed.


(* ********************************************************************** *)
(** ** On-the-fly hints *)

Parameter P Q : Prop.
Parameter P_is_true : P.
Parameter P_implies_Q : P -> Q.

Lemma demo_auto_tilde : P.
Proof using.
  autos~ P_is_true.
Qed.

Lemma demo_auto_star : P.
Proof using.
  autos* P_is_true, P_implies_Q.
Qed.








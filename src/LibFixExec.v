(**************************************************************************
* TLC: A library for Coq                                                  *
* Extensions to LibFix for recursive functions that compute in Coq        *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
From TLC Require Import LibTactics LibLogic LibReflect LibFun LibList
  LibInt LibNat LibRelation LibWf LibFix.

(* ********************************************************************** *)
(** * Function interation *)

(* ---------------------------------------------------------------------- *)
(** ** Definition of iteration *)

(** Definition with an eta-expansion, to avoid undesirable creation of
    numerous closures. *)

Fixpoint iter n A B (F:(A->B)->(A->B)) (f:A->B) (x:A) : B :=
  match n with
  | O => f x
  | S n' => F (iter n' F f) x
  end.

(** Alternative version, without the eta-expansion *)

Fixpoint iter' n A B (F:(A->B)->(A->B)) (f:A->B) : A -> B :=
  match n with
  | O => f
  | S n' => F (iter' n' F f)
  end.

Lemma iter'_eq_iter : iter' = iter.
Proof using.
  extens. intros n A B F f. induction n.
  { auto. }
  { extens. intros x. rewrite* IHn. }
Qed.

(* LATER: define exponentiation for improved efficiency *)


(* ---------------------------------------------------------------------- *)
(** ** Properties of iteration *)

(** On [iter'] *)

Lemma iter'_zero : forall A B (F:(A->B)->(A->B)) (f:A->B),
  iter' 0 F f = f.
Proof using. auto. Qed.

Lemma iter'_one : forall A B (F:(A->B)->(A->B)),
  iter' 1 F = F.
Proof using. auto. Qed.

Lemma iter'_succ : forall A B (F:(A->B)->(A->B)) (f:A->B) (n:nat),
  iter' (S n) F f = F (iter' n F f).
Proof using. auto. Qed.

Lemma iter'_succ_cont : forall A B (F:(A->B)->(A->B)) (f:A->B) (n:nat),
  iter' (S n) F f = iter' n F (F f).
Proof using.
  intros. induction n. { auto. }
  { rewrite iter'_succ. rewrite* IHn. }
Qed.

(** On [iter] *)

Lemma iter_zero : forall A B (F:(A->B)->(A->B)) (f:A->B),
  iter 0 F f = f.
Proof using. auto. Qed.

Lemma iter_one : forall A B (F:(A->B)->(A->B)),
  iter 1 F = F.
Proof using. auto. Qed.

Lemma iter_succ : forall A B (F:(A->B)->(A->B)) (f:A->B) (n:nat),
  iter (S n) F f = F (iter n F f).
Proof using. auto. Qed.

Lemma iter_succ_cont : forall A B (F:(A->B)->(A->B)) (f:A->B) (n:nat),
  iter (S n) F f = iter n F (F f).
Proof using. intros. rewrite <- iter'_eq_iter. apply iter'_succ_cont. Qed.

Lemma iter_swap : forall A B (F:(A->B)->(A->B)) (f:A->B) (n:nat),
  F (iter n F f) = iter n F (F f).
Proof using. intros. rewrite* <- iter_succ_cont. Qed.

Lemma iter_plus : forall A B (F:(A->B)->(A->B)) (f:A->B) (n m:nat),
  iter (n + m) F f = iter n F (iter m F f).
Proof using.
  intros. gen m. induction n; intros.
  { auto. }
  { simpl Nat.add. rewrite iter_succ. rewrite* IHn. }
Qed.

(** A partial fixed point of [F] is also a partial fixed point of [iter n F]. *)

Lemma iter_partial_fixed_point : forall A B (E:binary B) (F:(A->B)->(A->B)) (f:A-->B),
  partial_fixed_point E F f ->
  equiv E ->
  forall n, (n > 0)%nat ->
  partial_fixed_point E (iter n F) f.
Proof using.
  introv M HE. intros n. induction_wf IH: wf_lt n. intros Hn.
  tests Cn: (n = 1)%nat.
  { rewrite* iter_one. }
  { destruct n as [|n']. { false; math. }
    lets HE': pfun_equiv_equiv (dom f) HE.
    unfolds partial_fixed_point, fixed_point.
    intros g Hg. rewrite iter_succ_cont.
    specializes M g Hg.
    forwards~ N: (rm IH) n' (F g); try math. { applys* equiv_trans Hg M. }
    applys* equiv_trans M N. }
Qed.


(* ********************************************************************** *)
(** * Fixed point theorem for contractive functions *)

(** Partial functions *)

Lemma FixFun_fix_partial_iter : forall A (R:binary A) (P:A->Prop)
   B {IB:Inhab B} (F:(A->B)->(A->B)) (f:A->B),
  f = FixFun F -> wf R -> rec_contractive_noinv eq P F R ->
  (forall n x, P x -> f x = iter n F f x).
Proof using.
  introv Def Wf Cont.
  lets~ M: FixFun_fix_partial Cont. rewrite <- Def in M.
  intros n. induction n.
  { auto. }
  { intros x Px. simpl. applys eq_trans (F f x).
    { applys~ M. }
    { applys~ Cont. } }
Qed.

Arguments FixFun_fix_partial_iter [A] _ _ [B] {IB} [F] [f].

(** Total functions *)

Lemma FixFun_fix_iter : forall A (R:binary A) B {IB:Inhab B} (F:(A->B)->(A->B))
   (f:A->B),
  f = FixFun F -> wf R ->
  (forall f1 f2 x,
    (forall y, R y x -> f1 y = f2 y) ->
    F f1 x = F f2 x) ->
  (forall n x, f x = iter n F f x).
Proof using.
  intros. apply FixFun_fix_partial_iter with (IB:=IB) (R:=R) (P:=pred_true); auto.
  hnf; autos*.
Qed.

Arguments FixFun_fix_iter [A] _ [B] {IB} [F] [f].


(* ********************************************************************** *)
(** * Fixed point properties when [iter n F g] does not depend on [g] *)

(** [FixFun_iter_indep F n x] asserts that [iter n F g] does not
    depend on the choice of [g]. This is the case whenever recursive
    calls terminate at depth less than [n]. *)

Definition FixFun_iter_indep A B (F:(A->B)->(A->B)) (n:nat) (x:A) : Prop :=
  forall g1 g2, iter n F g1 x = iter n F g2 x.

(** Alternative characterization of [FixFun_iter_indep] *)

Lemma FixFun_iter_indep_of_image : forall A B (F:(A->B)->(A->B)) (n:nat) (x:A) (y:B),
  (forall g, iter n F g x = y) ->
  FixFun_iter_indep F n x.
Proof using. introv Hy. intros g1 g2. do 2 rewrite Hy. auto. Qed.

(** If [FixFun_iter_indep F n x] holds, then the fixed point equation holds
    at [x]. *)

Lemma FixFun_iter_indep_fix : forall A B (F:(A->B)->(A->B)) (n:nat) (x:A),
  FixFun_iter_indep F n x ->
  forall g, iter n F g x = F (iter n F g) x.
Proof using. introv Hx. intros g. rewrite iter_swap. applys Hx. Qed.


(* ********************************************************************** *)
(** * Executing functions using variants in the non-termination monad *)

(* ---------------------------------------------------------------------- *)
(** ** Fixed point combinator in the non-termination monad *)

(** [FixOpt] takes a functional expressed in the error monad, and returns
    its fixed point expressed in the non-termination monad. *)

Definition FixOpt A B (G:(A->option B)->(A->option B)) : nat->A->option B :=
  fix g (n:nat) (x:A) : option B :=
    match n with
    | O => None
    | S n' => G (g n') x
    end.

(** A function built using [FixOpt] for a given [n] can only return proper (non-None)
    results if [n > 0]. *)

Lemma FixOpt_eq_Some_inv_pos : forall A B (G:(A->option B)->(A->option B)) n x,
  FixOpt G n x <> None ->
  (n > 0)%nat.
Proof using. introv M. destruct n. { false* M. } { math. } Qed.


(* ---------------------------------------------------------------------- *)
(** ** Monotonicity property for functionals with respect to errors/timeouts *)

(** [option_fun_incl g1 g2], where [g1] and [g2] produce results of type [option],
    asserts that [g2] returns no less [Some] results than [g1], and always
    coherent with results produced by [g1]. *)

Definition option_fun_incl A B (g1 g2:(A->option B)) : Prop :=
  forall x y, g1 x = Some y -> g2 x = Some y.

(** [error_monad_monotonic G] asserts that applying [G] to two functions
    preserves the [option_fun_incl] property. *)

Definition error_monad_monotonic A B (G:(A->option B)->(A->option B)) : Prop :=
  forall g1 g2,
  option_fun_incl g1 g2 ->
  option_fun_incl (G g1) (G g2).

(** The monotonicity property [error_monad_monotonic G] is used in our development to
    argue that providing a larger recursion depth to [FixOpt] can only produce more
    results, and never invalidates results obtained at smaller depths. *)

Lemma FixOpt_mono_succ : forall A B (G:(A->option B)->(A->option B)) n x y,
  error_monad_monotonic G ->
  FixOpt G n x = Some y ->
  FixOpt G (S n) x = Some y.
Proof using.
  introv HG EQ. gen x y. induction n; introv EQ.
  { false. }
  { simpls. applys HG EQ. intros g1 g2. applys IHn. }
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Relationship between a function and its monadic reformulation *)

(** [is_monadic_variant f g] asserts that [g] is a reformulation of the function [f]
    in the error monad (with respect to correctness only, not w.r.t. to completeness). *)

Definition is_monadic_variant A B (f : A -> B) (g : A -> option B) : Prop :=
  forall x z, g x = Some z -> f x = z.

(** [is_ho_monadic_variant F G] asserts that the functional [G] is a reformulation of
    the functional [F], as a combinator in the error monad (again, w.r.t. correctness only). *)

Definition is_ho_monadic_variant A B
 (F : (A->B)->(A->B)) (G : (A->option B)->(A->option B)) : Prop :=
  forall f g,
  is_monadic_variant f g ->
  is_monadic_variant (F f) (G g).

(** The following lemma asserts that if [is_ho_monadic_variant F G], then
    [FixOpt Fopt n x] is the monadic reformulation of [iter n F h], for any [h]. *)

Lemma iter_of_is_ho_monadic_variant : forall A B
 (F : (A->B)->(A->B)) (G : (A->option B)->(A->option B)),
  is_ho_monadic_variant F G ->
  forall n h,
  is_monadic_variant (iter n F h) (FixOpt G n).
Proof using.
 introv HF. intros n. induction n; intros h x y EQ.
  { false. }
  { simpls. applys HF EQ. intros a b Hab. applys* IHn. }
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Termination property and call-dependencies in the non-termination monad *)

(** [terminates G x] asserts that the function [FixOpt Fopt] returns a
    proper output on the input [x], meaning that its execution does not
    run out of fuel. *)

Definition terminates A B (G:(A->option B)->(A->option B)) (x:A) : Prop :=
  exists n, FixOpt G n x <> None.

(** [captures_dep f Fopt R] asserts that, for the functional [G] written in the
    error monad, the relation [R] describes (technically over-approximates)
    the recursive call graph: if a call on input [x] involves a recursive on input [y],
    then [R y x] holds. The argument [f] is used by nest-recursive functions,
    for which the argument of a recursive call might depend on the result of another
    recursive call. In that case, we need to exploit the information that the
    function [g] used for performing recursive calls in [G] indeed corresponds to
    the optimal fixed point [f] of [F]. *)

Definition captures_dep A B (f:A->B) (G:(A->option B)->(A->option B)) (R : (A->B)->A->A->Prop) : Prop :=
  forall g, is_monadic_variant f g ->
  forall x y, R f y x -> G g x <> None -> g y <> None.

(** [captures_dep G R] guarantees in particular that, when [R y x] holds,
    [FixOpt Fopt (S n) x <> None] implies [FixOpt Fopt n y <> None]. *)

Lemma captures_dep_on_FixOpt : forall A B f (G:(A->option B)->(A->option B)) (R : (A->B)->A->A->Prop) (n:nat),
  captures_dep f G R ->
  is_monadic_variant f (FixOpt G n) ->
  forall x y,
  R f y x ->
  FixOpt G (S n) x <> None ->
  FixOpt G n y <> None.
Proof using. introv M Hf HR HN. simpl in HN. applys M Hf HR HN. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Fixed point theorems for terminating executions *)

(** Major theorem relating the optimal fixed point combinator [FixFun] with the iterated
    fixed point combinators [FixOpt] and [iter]:
    on the domain where the functional in the non-termination monad terminates in n steps,
    the functional [iter n F g] is a fixed point of [F], for any continuation [g].
    Morever, this fixed point is consistent with any other fixed point of [F]. *)

Lemma generally_consistent_partial_fixed_point_on_terminates : forall A B (F:(A->B)->(A->B)) G (n:nat),
  is_ho_monadic_variant F G ->
  error_monad_monotonic G ->
  let D x := FixOpt G n x <> None in
  forall g, generally_consistent_partial_fixed_point eq F (Build_partial (iter n F g) D).
Proof using.
  introv HFG HG. intros D g. split.
  { intros h Hh. simpls. unfolds pfun_equiv.
    intros x Dx. case_eq (FixOpt G n x); [|auto_false]. intros y Hxy.
    applys eq_trans y.
    { rewrite~ <- Hh. applys iter_of_is_ho_monadic_variant HFG Hxy. }
    { lets M: HFG h (FixOpt G n) x y.
      { clears x y. intros x y Hxy. rewrite <- Hh; [|auto_false].
        applys iter_of_is_ho_monadic_variant HFG Hxy. }
    rewrite~ M. applys FixOpt_mono_succ HG Hxy. } }
  { intros [h D'] Hh.
    intros x (Dx&D'x). unfolds pfun_equiv. simpls.
    case_eq (FixOpt G n x); [|auto_false]. intros y Hxy.
    applys eq_trans y. { applys iter_of_is_ho_monadic_variant HFG Hxy. }
    symmetry. gen x y. gen n. intros n.
    (* forall n x Y, FixOpt G n x <> None -> D' x -> FixOpt G n x = Some y -> h x = y
       -- Where [D'] is the domain of another arbitrary fixed point named [h] *)
    induction_wf IH: lt_wf n. intros.
    { set (h' := fun x => If D' x then h x else iter n F g x).
      specializes Hh h' __.
      { clears x y. unfolds pfun_equiv. simpls. intros x D'x. unfold h'. case_if; auto. }
      lets~ Hhx: Hh x __. unfold h' at 1 in Hhx. case_if. rewrites (rm Hhx ).
      lets Hn: FixOpt_eq_Some_inv_pos Dx. destruct n as [|n']; [false;math|].
      lets M: HFG h' (FixOpt G n') x y.
      { clears x y. intros x y Hxy. unfold h'. case_if.
        { applys IH n'; auto_false. }
        { lets Hxy': FixOpt_mono_succ HG Hxy.
          applys iter_of_is_ho_monadic_variant HFG Hxy'. } }
      { rewrite~ M. } } }
Qed.

(** We next state two corollaries of the major theorem.
    (1) If [FixOpt G n x] produces a proper output, then the value associated to [x]
        by the optimal fixed point combinator, namely [FixFun F x], can be computed
        using the iteration of the functional [F]: the result is equal to
        [iter n F g x], for an arbitrary [g].
    (2) Furthermore, if [y] denotes the result produced by [FixOpt G n x], then
        [iter n F g x] is equal to [y]. *)

Lemma FixFun_eq_iter_on_terminates : forall A B {IB:Inhab B} f (F:(A->B)->(A->B)) G (n:nat) (x:A),
  f = FixFun F ->
  is_ho_monadic_variant F G ->
  error_monad_monotonic G ->
  FixOpt G n x <> None ->
  forall g, f x = iter n F g x.
Proof using.
  introv Hf HFG HG Dx. intros g.
  lets M: generally_consistent_partial_fixed_point_on_terminates HFG HG g.
  applys* FixFunMod_inv_at M. { applys equiv_eq. }
Qed.

Lemma FixFun_is_monadic_variant_FixOpt : forall A B {IB:Inhab B} f (F:(A->B)->(A->B)) G,
  f = FixFun F ->
  is_ho_monadic_variant F G ->
  error_monad_monotonic G ->
  forall n, is_monadic_variant f (FixOpt G n).
Proof using.
  introv Hf HFG HG Hxy. rewrites (>> FixFun_eq_iter_on_terminates n x Hf HFG HG f).
  { auto_false. } { applys iter_of_is_ho_monadic_variant HFG Hxy. }
Qed.

(** Expanded version of the above, useful for the end-user *)

Lemma FixFun_eq_FixOpt : forall A B {IB:Inhab B} f (F:(A->B)->(A->B)) G (n:nat) (x:A) (z:B),
  f = FixFun F ->
  is_ho_monadic_variant F G ->
  error_monad_monotonic G ->
  FixOpt G n x = Some z ->
  f x = z.
Proof using. introv Hf HFG HG Hxy. applys* FixFun_is_monadic_variant_FixOpt. Qed.

(** Next lemma contains the key proof, factorizing the arguments for the two final
    induction principles. *)

Lemma FixFun_fix_ter_common : forall A B {IB:Inhab B} f (F:(A->B)->(A->B)) (P:A->B->Prop)
   (G:(A->option B)->(A->option B)),
  f = FixFun F ->
  is_ho_monadic_variant F G ->
  error_monad_monotonic G ->
  (forall n x, FixOpt G (S n) x <> None ->
    let h := iter n F f in
    (forall y, FixOpt G n y <> None -> P y (h y)) ->
    P x (F h x)) ->
  forall x, terminates G x -> P x (f x).
Proof using.
  introv Hf HFG HG HI Hx.
  destruct Hx as (n&Hx). case_eq (FixOpt G n x); [|auto_false]. intros y Hy.
  lets MG: iter_of_is_ho_monadic_variant HFG.
  asserts HFnx: (FixFun_iter_indep F n x).
  { intros g1 g2. rewrites (>> MG g1 Hy). rewrites* (>> MG g2 Hy). }
  rewrites~ (>> FixFun_eq_iter_on_terminates x Hf HFG HG Hx f).
  lets Hn: FixOpt_eq_Some_inv_pos Hx.
  clear Hy HFnx y. gen Hn x.
  (* forall (n > 0), forall x, FixOpt G n x <> None -> P x (iter n F f x) *)
  induction_wf IH: wf_lt n. intros Hn x Hx.
  destruct n as [| n']; [false;math|]. simpl. applys* HI.
  intros y Hy. lets Hn': FixOpt_eq_Some_inv_pos Hy.
  applys IH Hy; try math.
Qed.

(** The following fixed point induction principle asserts that, on the domain of input
    values [x] on which [FixFun Fopt] terminates with a proper output, one can prove a
    property [P] about the fixed point [f] by assuming the property to hold of
    recursive calls. These recursive calls as captured by the relation [R]. *)

Lemma FixFun_fix_ter : forall A B {IB:Inhab B} (f:A->B) (F:(A->B)->(A->B)) (P:A->B->Prop)
   (G:(A->option B)->(A->option B)) (R:(A->B)->A->A->Prop),
  f = FixFun F ->
  is_ho_monadic_variant F G ->
  error_monad_monotonic G ->
  captures_dep f G R ->
  (forall x, terminates G x ->
    (forall y, R f y x -> P y (f y)) ->
    P x (F f x)) ->
  forall x, terminates G x -> P x (f x).
Proof using.
  introv Hf HFG HG HR HI Hx.
  applys FixFun_fix_ter_common Hf HFG HG Hx.
  { clears x. intros n x Hx h Hy. applys_eq HI.
    { case_eq (FixOpt G (S n) x); [|auto_false]. intros z Hz.
      subst h. applys eq_trans z.
      { applys iter_of_is_ho_monadic_variant HFG f Hz. }
      { symmetry. simpl in Hz. applys HFG Hz. applys* FixFun_is_monadic_variant_FixOpt. } }
    { exists* (S n). }
    { intros y Ryx. lets HGy: captures_dep_on_FixOpt HR Ryx Hx.
      { applys FixFun_is_monadic_variant_FixOpt Hf HFG HG. }
      { applys_eq (>> Hy HGy). applys FixFun_eq_iter_on_terminates Hf HFG HG HGy. } } }
Qed.

(** The following fixed point induction principle is a variant of the former, that does
    not need to worry about characterizing recursive calls using a relation [R],
    provided that the property [P] of interest is "satisfiable", in the sense that the
    user is able to provide a function [h] satisfying [forall x, P x (h x)]. *)

Lemma FixFun_fix_ter_sat : forall A B {IB:Inhab B} f (F:(A->B)->(A->B)) (P:A->B->Prop)
   (G:(A->option B)->(A->option B)),
  f = FixFun F ->
  (exists h, forall x, P x (h x)) ->
  is_ho_monadic_variant F G ->
  error_monad_monotonic G ->
  (forall h x, terminates G x -> (forall y, P y (h y)) -> P x (F h x)) ->
  forall x, terminates G x -> P x (f x).
Proof using.
  introv Hf (h0&Hh0) HFG HG HI Hx.
  applys FixFun_fix_ter_common Hf HFG HG Hx. clears x.
  { intros n x Hx h Hy. lets Px: HI (fun y => If FixOpt G n y <> None then h y else h0 y) x __ __.
    { exists* (S n). }
    { intros y. case_if. { applys* Hy. } { applys Hh0. } }
    { applys_eq Px. clear Px. subst h.
      case_eq (FixOpt G (S n) x); [|auto_false]. intros z Hz.
      applys eq_trans z.
      { applys iter_of_is_ho_monadic_variant HFG (S n) f Hz. }
      { symmetry. simpl in Hz. applys HFG Hz. intros a b Hab.
        case_if. applys iter_of_is_ho_monadic_variant HFG n Hab. } } }
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Another theorem, not involving the error monad *)

(** Assume that the property [P] is satisfied by an arbitrary function [h].
    Then, one can establish the property [P] for [iter n F], simply by showing
    the implication: forall [h] satisfying [P], it is the case that [F h] satisfies [P]. *)

Lemma iter_fix_sat : forall A B (F:(A->B)->(A->B)) (P:A->B->Prop) (h:A->B),
  (forall x, P x (h x)) ->
  (forall h x, (forall y, P y (h y)) -> P x (F h x)) ->
  forall n x, P x (iter n F h x).
Proof using.
  introv Hh HI. induction n; intros; simpl.
  { applys Hh. }
  { applys HI. applys IHn. }
Qed.


(* ********************************************************************** *)
(** * Error monad constructors *)

(** We use the standard monadic constructors to express functionals in the
    non-termination monad. *)

Definition Return A (x:A) : option A :=
  Some x.

Definition Bind A B (o:option A) (k:A->option B) : option B :=
  match o with
  | None => None
  | Some a => k a
  end.

Declare Scope error_monad_scope.
Notation "'ret%' x" := (Return x) (at level 67) : error_monad_scope.
Notation "'let%' a := o 'in' k" := (Bind o (fun a => k)) (at level 67) : error_monad_scope.
Open Scope error_monad_scope.

(** Inversion lemmas *)

Lemma Bind_monotonic : forall A B (o1 o2:option A) (k1 k2:A->option B) r,
  Bind o1 k1 = Some r ->
  (forall s, o1 = Some s -> o2 = Some s) ->
  (forall a, k1 a = Some r -> k2 a = Some r) ->
  Bind o2 k2 = Some r.
Proof using.
  introv M Ha Hk. destruct o1 as [a|]; tryfalse.
  forwards~ ->: Ha a. simpls. auto.
Qed.

Lemma Return_Some_inv : forall A (x r:A),
  Return x = Some r ->
  x = r.
Proof using. introv E. inverts* E. Qed.

Lemma Binds_Some_inv : forall A B o (k:A->option B) r,
  Bind o k = Some r ->
  exists a, o = Some a /\ k a = Some r.
Proof using. introv E. destruct o; tryfalse. { inverts* E. } Qed.

Lemma Binds_not_None_inv : forall A B o (k:A->option B),
  Bind o k <> None ->
  exists a, o = Some a /\ k a <> None.
Proof using. introv E. destruct o; tryfalse*. { exists* a. } Qed.


(* ********************************************************************** *)
(** * Tactics *)

(** [FixCall h] is a helper tactic for exploiting assumptions about recursive calls. *)

Ltac FixCall h :=
  match goal with IH: context [h] |- context[h ?x] =>
    forwards: IH x; try eauto end.


(* ********************************************************************** *)
(** * Demo *)

(* ---------------------------------------------------------------------- *)
(** ** Fib with boolean definition *)

Module Fib.
Open Scope nat_scope.

Definition Fib fib (n:nat) : nat :=
  if le_dec n 1
    then 1
    else fib (n-1) + fib (n-2).

Definition fib := FixFun Fib.

(* monadic version -- should be automatically generated *)
Definition FibOpt fib (n:nat) : option nat :=
  if le_dec n 1
    then ret% 1
    else let% a := fib (n-1) in
         let% b := fib (n-2) in
         ret% a + b.

(* monotonicity lemma -- should be automatically generated *)
Lemma FibOpt_mono : error_monad_monotonic FibOpt.
Proof using.
  intros g1 g2 M n r E. unfolds FibOpt.
  case_if.
  { auto. }
  { applys Bind_monotonic (rm E). { applys M. } intros a E.
    applys Bind_monotonic (rm E). { applys M. } intros b E.
    auto. }
Qed.

(* simulation lemma -- should be automatically generated *)
Lemma FibOpt_simu : is_ho_monadic_variant Fib FibOpt.
Proof using.
  intros f g M. intros n r E. unfolds FibOpt, Fib.
  case_if.
  { lets ?: Return_Some_inv (rm E). congruence. }
  { lets (a&Ha&E2): Binds_Some_inv (rm E).
    lets Ea: M Ha.
    lets (b&Hb&E3): Binds_Some_inv (rm E2).
    lets Eb: M Hb.
    lets E4: Return_Some_inv (rm E3).
    congruence. }
Qed.

(* dependency relation -- should be automatically generated *)
Definition FibRec (fib:nat->nat) (n':nat) (n:nat) : Prop :=
  if le_dec n 1
    then False
    else (n' = n-1) \/
         let a := fib (n-1) in
         (n' = n-2) \/
         let b := fib (n-2) in
         False.

(* dependency lemma -- should be automatically generated *)
Lemma FibRec_dep : captures_dep fib FibOpt FibRec.
Proof using.
  intros g _ n n' HR E. unfolds FibOpt, FibRec.
  case_if.
  (* { false. } *)
  { lets (a&Ha&E2): Binds_not_None_inv (rm E).
    lets (b&Hb&E3): Binds_not_None_inv (rm E2).
    destruct HR as [|[|]]; congruence. }
Qed.

(** Demo: computing with (FibOpt] to derive a result of [fib].
    Here [10%nat] is an arbitrary, sufficiently large bound on the depth. *)

Lemma fib5 : exists r, fib 5 = r.
Proof using.
  exists. applys FixFun_eq_FixOpt 10%nat FibOpt_simu FibOpt_mono; [reflexivity|].
  cbv. (* evaluates [FixOpt FibOpt 10 5] to [Some 8] *)
  reflexivity.
Qed.

(** Demo: proving a property of [fib], e.g. that it returns nonzero values,
    whenever the computation using [FibOpt] terminates at some finite depth. *)

Lemma fib_pos : forall n, terminates FibOpt n -> fib n > 0.
Proof using.
  intros.
  applys FixFun_fix_ter (fun (x y:nat) => y > 0) FibOpt_simu FibOpt_mono FibRec_dep; auto.
  clears n. intros n _ IH. unfolds Fib, FibRec.
  case_if.
  { math. }
  { forwards* IH1: IH (n-1). forwards* IH2: IH (n-2). math. }
    (* same as the line above using more automation:  { do 2 FixCall h. math. }  *)
Qed.

(** Demo: variant of the above proof, exploiting the fact that the property
    [f n > 0] is satisfiable by at least one function [f]. This alternative
    proof does not require reasoning about dependencies of recursive calls,
    and does not need the statement of [FibRec] and [FibRec_dep].  *)

Lemma fib_pos' : forall n, terminates FibOpt n -> fib n > 0.
Proof using.
  intros.
  applys FixFun_fix_ter_sat (fun (x y:nat) => y > 0) FibOpt_simu FibOpt_mono; auto.
  { exists (fun (_:nat) => 1). math. }
  clears n. intros h n Hn IH. unfolds Fib.
  case_if.
  { math. }
  { forwards* IH1: IH (n-1). forwards* IH2: IH (n-2). math. }
    (* same as the line above using more automation:  { do 2 FixCall h. math. }  *)
Qed.

(** Demo: using [iter_fix_sat] to prove properties of [iter m Fib]. *)

Lemma iter_Fib_pos : forall m n, iter m Fib (fun (_:nat) => 1) n > 0.
Proof using.
  intros. applys iter_fix_sat. { math. }
  clear n. intros h n IH. unfold Fib.
  case_if.
  { math. }
  { forwards* IH1: IH (n-1). forwards* IH2: IH (n-2). math. }
Qed.

End Fib.

(* ---------------------------------------------------------------------- *)
(** ** Fib with non-constructive definition *)

Module FibClassical.
Open Scope nat_scope.

Definition Fib fib (n:nat) : nat :=
  If n <= 1 (* instead of: if le_dec n 1 *)
    then 1
    else fib (n-1) + fib (n-2).

Definition fib := FixFun Fib.

(* monadic version -- should be automatically generated *)
Definition FibOpt fib (n:nat) : option nat :=
  if le_dec n 1
    then ret% 1
    else let% a := fib (n-1) in
         let% b := fib (n-2) in
         ret% a + b.

(* monotonicity lemma -- should be automatically generated *)
Lemma FibOpt_mono : error_monad_monotonic FibOpt.
Proof using.
  intros g1 g2 M n r E. unfolds FibOpt.
  case_if.
  { auto. }
  { applys Bind_monotonic (rm E). { applys M. } intros a E.
    applys Bind_monotonic (rm E). { applys M. } intros b E.
    auto. }
Qed.

(* simulation lemma -- should be automatically generated *)
Lemma FibOpt_simu : is_ho_monadic_variant Fib FibOpt.
Proof using.
  intros f g M. intros n r E. unfolds FibOpt, Fib.
  do 2 case_if.
  { lets ?: Return_Some_inv (rm E). congruence. }
  { lets (a&Ha&E2): Binds_Some_inv (rm E).
    lets Ea: M Ha.
    lets (b&Hb&E3): Binds_Some_inv (rm E2).
    lets Eb: M Hb.
    lets E4: Return_Some_inv (rm E3).
    congruence. }
Qed.

(* dependency relation -- should be automatically generated *)
Definition FibRec (fib:nat->nat) (n':nat) (n:nat) : Prop :=
  if le_dec n 1
    then False
    else (n' = n-1) \/
         let a := fib (n-1) in
         (n' = n-2) \/
         let b := fib (n-2) in
         False.

(* dependency lemma -- should be automatically generated *)
Lemma FibRec_dep : captures_dep fib FibOpt FibRec.
Proof using.
  intros g _ n n' HR E. unfolds FibOpt, FibRec.
  case_if.
  (* { false. } *)
  { lets (a&Ha&E2): Binds_not_None_inv (rm E).
    lets (b&Hb&E3): Binds_not_None_inv (rm E2).
    destruct HR as [|[|]]; congruence. }
Qed.

(** Demo: computing with [FibOpt] to derive a result of [fib].
    Here [10%nat] is an arbitrary, sufficiently large bound on the depth. *)

Lemma fib5 : exists r, fib 5 = r.
Proof using.
  exists. applys FixFun_eq_FixOpt 10%nat FibOpt_simu FibOpt_mono; [reflexivity|].
  cbv. (* evaluates [FixOpt FibOpt 10 5] to [Some 8] *)
  reflexivity.
Qed.

(** Demo: proving a property of [fib], e.g. that it returns nonzero values,
    whenever the computation using [FibOpt] terminates at some finite depth. *)

Lemma fib_pos : forall n, terminates FibOpt n -> fib n > 0.
Proof using.
  intros.
  applys FixFun_fix_ter (fun (x y:nat) => y > 0) FibOpt_simu FibOpt_mono FibRec_dep; auto.
  clears n. intros n _ IH. unfolds Fib, FibRec.
  do 2 case_if.
  { math. }
  { forwards* IH1: IH (n-1). forwards* IH2: IH (n-2). math. }
    (* same as the line above using more automation:  { do 2 FixCall h. math. }  *)
Qed.

(** Demo: variant of the above proof, exploiting the fact that the property
    [f n > 0] is satisfiable by at least one function [f]. This alternative
    proof does not require reasoning about dependencies of recursive calls,
    and does not need the statement of [FibRec] and [FibRec_dep].  *)

Lemma fib_pos' : forall n, terminates FibOpt n -> fib n > 0.
Proof using.
  intros.
  applys FixFun_fix_ter_sat (fun (x y:nat) => y > 0) FibOpt_simu FibOpt_mono; auto.
  { exists (fun (_:nat) => 1). math. }
  clears n. intros h n Hn IH. unfolds Fib.
  case_if.
  { math. }
  { forwards* IH1: IH (n-1). forwards* IH2: IH (n-2). math. }
    (* same as the line above using more automation:  { do 2 FixCall h. math. }  *)
Qed.

(** Demo: using [iter_fix_sat] to prove properties of [iter m Fib]. *)

Lemma iter_Fib_pos : forall m n, iter m Fib (fun (_:nat) => 1) n > 0.
Proof using.
  intros. applys iter_fix_sat. { math. }
  clear n. intros h n IH. unfold Fib.
  case_if.
  { math. }
  { forwards* IH1: IH (n-1). forwards* IH2: IH (n-2). math. }
Qed.

End FibClassical.

(* ---------------------------------------------------------------------- *)
(** ** Nested recursion *)

Section Nest.
Open Scope nat_scope.

Definition Nest nest (n:nat) : nat :=
  if le_dec n 1
    then 0
    else nest (nest (n-1) + nest (n-2)).

Definition nest := FixFun Nest.

(* monadic version -- should be automatically generated *)
Definition NestOpt nest (n:nat) : option nat :=
  if le_dec n 1
    then ret% 0
    else let% a := nest (n-1) in
         let% b := nest (n-2) in
         nest (a + b).

(* monotonicity lemma -- should be automatically generated *)
Lemma NestOpt_mono : error_monad_monotonic NestOpt.
Proof using.
  intros g1 g2 M n r E. unfolds NestOpt.
  case_if.
  { auto. }
  { applys Bind_monotonic (rm E). { applys M. } intros a E.
    applys Bind_monotonic (rm E). { applys M. } intros b E.
    auto. }
Qed.

(* simulation lemma -- should be automatically generated *)
Lemma NestOpt_simu : is_ho_monadic_variant Nest NestOpt.
Proof using.
  intros f g M. intros n r E. unfolds NestOpt, Nest.
  case_if.
  { lets ?: Return_Some_inv (rm E). congruence. }
  { lets (a&Ha&E2): Binds_Some_inv (rm E).
    lets Ea: M Ha.
    lets (b&Hb&E3): Binds_Some_inv (rm E2).
    lets Eb: M Hb.
    lets Ec: M E3.
    congruence. }
Qed.

(* dependency relation -- should be automatically generated *)
Definition NestRec (nest:nat->nat) (n':nat) (n:nat) : Prop :=
  if le_dec n 1
    then False
    else (n' = n-1) \/
         let a := nest (n-1) in
         (n' = n-2) \/
         let b := nest (n-2) in
         (n' = a+b) \/
         False.

(* dependency lemma -- should be automatically generated *)
Lemma NestRec_dep : captures_dep nest NestOpt NestRec.
Proof using.
  intros g Hg n n' HR E. unfolds NestOpt, NestRec.
  case_if. (* 1:{ false. } *)
  { lets (a&Ha&E2): Binds_not_None_inv (rm E). lets Ea: Hg Ha.
    lets (b&Hb&E3): Binds_not_None_inv (rm E2). lets Eb: Hg Hb.
    destruct HR as [|[|[|]]]; try congruence. }
Qed.

(** Demo: computing with [NestOpt] to derive a result of [nest].
    Here [10%nat] is an arbitrary, sufficiently large bound on the depth. *)

Lemma nest5 : exists r, nest 2 = r.
Proof using.
  exists. applys FixFun_eq_FixOpt 10%nat NestOpt_simu NestOpt_mono; [reflexivity|].
  cbv. (* evaluates [FixOpt NestOpt 10 5] to [Some 0] *)
  reflexivity.
Qed.

(** Demo: proving a property of [nest], e.g. that it returns zero values,
    whenever the computation using [NestOpt] terminates at some finite depth. *)

Lemma nest_zero : forall n, terminates NestOpt n -> nest n = 0.
Proof using.
  intros.
  applys FixFun_fix_ter (fun (x y:nat) => y = 0) NestOpt_simu NestOpt_mono NestRec_dep; auto.
  clears n. intros n _ IH.
  unfolds Nest, NestRec.
  case_if.
  { math. }
  { apply IH. eauto. } (* no need to investigate all branches *)
Qed.

(** Demo: variant of the above proof, exploiting the fact that the property
    [f n = 0] is satisfiable by at least one function [f]. This alternative
    proof does not require reasoning about dependencies of recursive calls,
    and does not need the statement of [NestRec] and [NestRec_dep].  *)

Lemma nest_zero' : forall n, terminates NestOpt n -> nest n = 0.
Proof using.
  intros.
  applys FixFun_fix_ter_sat (fun (x y:nat) => y = 0) NestOpt_simu NestOpt_mono; auto.
  { exists (fun (_:nat) => 0). math. }
  clears n. intros h n Hn IH. unfolds Nest.
  case_if.
  { math. }
  { applys IH. }
Qed.

End Nest.


(* ---------------------------------------------------------------------- *)
(** ** Syracuse sequence -- conjectured termination *)

Module Syracuse.
Open Scope nat_scope.
Import Nat.

Definition Syr syr (n:nat) : nat :=
  if eq_nat_dec n 1 then
    0
  else if even n then
    1 + syr(n/2)
  else 
    1 + syr(3*n+1).

(* ALTERNATIVE
Definition Syr syr (n:nat) : nat :=
  if eq_nat_dec n 1 
    then 0
    else 1 + syr (if even n then (n/2) else (3*n+1)).*)

Definition syr := FixFun Syr.

(* monadic version -- should be automatically generated *)
Definition SyrOpt syr (n:nat) : option nat :=
  if eq_nat_dec n 1 then
    ret% 0
  else if even n then
    let% r := syr(n/2) in
    ret% 1 + r
  else 
    let% r := syr(3*n+1) in
    ret% 1 + r.

(* monotonicity lemma -- should be automatically generated *)
Lemma SyrOpt_mono : error_monad_monotonic SyrOpt.
Proof using.
  intros g1 g2 M n r E. unfolds SyrOpt.
  repeat case_if.
  { auto. }
  { applys* Bind_monotonic E. }
  { applys* Bind_monotonic E. }
Qed.

(* simulation lemma -- should be automatically generated *)
Lemma SyrOpt_simu : is_ho_monadic_variant Syr SyrOpt.
Proof using.
  intros f g M. intros n r E. unfolds SyrOpt, Syr.
  repeat case_if.
  { lets*: Return_Some_inv (rm E). }
  { lets (a&Ha&E2): Binds_Some_inv (rm E).
    lets Ea: M Ha.
    lets E4: Return_Some_inv (rm E2).
    congruence. }
  { lets (a&Ha&E2): Binds_Some_inv (rm E).
    lets Ea: M Ha.
    lets E4: Return_Some_inv (rm E2).
    congruence. }
Qed.

(* dependency relation -- should be automatically generated *)
Definition SyrRec (syr:nat->nat) (n':nat) (n:nat) : Prop :=
  if eq_nat_dec n 1 then
    False
  else if even n then
    (n' = n/2)
  else
    (n' = 3*n+1).

(* dependency lemma -- should be automatically generated *)
Lemma SyrRec_dep : captures_dep syr SyrOpt SyrRec.
Proof using.
  intros g _ n n' HR E. unfolds SyrOpt, SyrRec.
  repeat case_if.
  (* { false. } *)
  { lets (a&Ha&E2): Binds_not_None_inv (rm E). congruence. }
  { lets (a&Ha&E2): Binds_not_None_inv (rm E). congruence. }
Qed.

(** Demo: computing with [SyrOpt] to derive a result of [syr].
    Here [100%nat] is an arbitrary, sufficiently large bound on the depth. 
    
    7 -> 22 -> 11 -> 34 -> 17 -> 52 -> 26 -> 13 -> 40 ->
     20 -> 10 -> 5 -> 16 -> 8 -> 4 -> 2 -> 1
    reaches 1 in 16 steps, therefore  [syr 7 = 16] *)

Lemma syr7 : exists r, syr 7 = r.
Proof using.
  exists. applys FixFun_eq_FixOpt 100%nat SyrOpt_simu SyrOpt_mono; [reflexivity|].
  cbv. (* evaluates [FixOpt SyrOpt 10 5] to [Some 8] *)
  reflexivity.
Qed.

(** Demo: computing [syr 0] which loops infinitely, as [0] is not equal to one,
    is even, and thus leads to the recursive evaluation of [syr 0].
    Here [100%nat] is an arbitrary depth. After 100 calls, the function [SyrOpt]
    returns [None]. *)

Lemma syr0 : exists r, syr 0 = r.
Proof using.
  exists. applys FixFun_eq_FixOpt 100%nat SyrOpt_simu SyrOpt_mono; [reflexivity|].
  cbv. (* produces the unprovable goal [None = Some ?r] *)
Abort.

(** Demo: proving a property of [syr], e.g. that it returns nonzero values,
    whenever its input is greater than 1, and [SyrOpt] terminates at some finite depth. *)

Lemma syr_pos : forall n, n > 1 -> terminates SyrOpt n -> syr n > 0.
Proof using.
  intros.
  applys FixFun_fix_ter (fun (x y:nat) => x > 1 -> y > 0) 
   SyrOpt_simu SyrOpt_mono SyrRec_dep; auto.
  clears n. intros n _ IH Hn. unfolds Syr, SyrRec.
  repeat case_if.
  { false. math. }
  { math. }
  { math. }
Qed.

End Syracuse.


(* ---------------------------------------------------------------------- *)
(** ** Lambda-term evaluator -- undecidable termination *)

Module Evaluator.

(** Representation of variables by names (numbers, for simplicity) *)

Definition var : Type := nat.

Definition var_eq := eq_nat_dec.

(** Grammar of values and terms *)

Inductive val : Type :=
  | val_nat : nat -> val
  | val_clo : var -> trm -> val
  | val_error : val

with trm : Type :=
  | trm_val : val -> trm
  | trm_var : var -> trm
  | trm_abs : var -> trm -> trm
  | trm_app : trm -> trm -> trm.

Coercion trm_val : val >-> trm.

#[global]
Instance Inhab_val : Inhab val.
Proof using. intros. apply (Inhab_of_val val_error). Qed.

(** Substitution *)

Fixpoint subst (x:var) (v:val) (t:trm) : trm :=
  let s := subst x v in
  match t with
  | trm_val v => t
  | trm_var y => if var_eq x y then trm_val v else t
  | trm_abs y t3 => trm_abs y (if var_eq x y then t3 else s t3)
  | trm_app t1 t2 => trm_app (s t1) (s t2)  
  end.

(** Evaluation function *)

Definition is_error (v:val) : bool :=
  match v with 
  | val_error => true
  | _ => false
  end.

Definition Eval eval (t:trm) : val :=
  match t with
  | trm_val v => v
  | trm_abs x t1 => val_clo x t1
  | trm_var x => val_error (* unbound variable *)
  | trm_app t1 t2 => 
      let v1 := eval t1 in
      let v2 := eval t2 in
      if is_error v2 then val_error else
      match v1 with
      | val_clo x t3 => eval (subst x v2 t3)
      | _ => val_error (* application of a non-functional value *)
      end
  end.

Definition eval := FixFun Eval.

(* monadic version -- should be automatically generated *)
Definition EvalOpt eval (t:trm) : option val :=
  match t with
  | trm_val v => ret% v
  | trm_abs x t1 => ret% (val_clo x t1)
  | trm_var x => ret% val_error 
  | trm_app t1 t2 => 
      let% v1 := eval t1 in
      let% v2 := eval t2 in
      if is_error v2 then ret% val_error else
      match v1 with
      | val_clo x t3 => eval (subst x v2 t3)
      | _ => ret% val_error 
      end
  end.

(* Note: alternatively, one could simply return None instead of producing val_error.
   However, doing so would not distinguish between non-terminating terms and terms
   that terminate on an error. *)


(* monotonicity lemma -- should be automatically generated *)
Lemma EvalOpt_mono : error_monad_monotonic EvalOpt.
Proof using.
  intros g1 g2 M t r E. unfolds EvalOpt.
  destruct t; auto.
  { applys* Bind_monotonic (rm E). intros a Ea. 
    applys* Bind_monotonic (rm Ea). intros b Eb.
    case_if.
    { auto. }
    { destruct a; auto. } } 
Qed.

(* simulation lemma -- should be automatically generated *)
Lemma EvalOpt_simu : is_ho_monadic_variant Eval EvalOpt.
Proof using.
  intros f g M. intros t r E. unfolds EvalOpt, Eval.
  destruct t; try (lets*: Return_Some_inv (rm E)).
  { lets (a&Ha&E2): Binds_Some_inv (rm E). lets Ea: M Ha.
    lets (b&Hb&E3): Binds_Some_inv (rm E2). lets Eb: M Hb.
    rewrite Eb. case_if.
    { lets*: Return_Some_inv (rm E3). }
    { rewrite Ea. destruct a. 
      { lets*: Return_Some_inv (rm E3). }
      { applys M. congruence. }
      { lets*: Return_Some_inv (rm E3). } } }
Qed.

(* dependency relation -- should be automatically generated *)
Definition EvalRec (eval:trm->val) (t':trm) (t:trm) : Prop :=
  match t with
  | trm_val v => False
  | trm_abs x t1 => False
  | trm_var x => False
  | trm_app t1 t2 => 
      (t' = t1) \/
      let v1 := eval t1 in
      (t' = t2) \/
      let v2 := eval t2 in
      if is_error v2 then False else
      match v1 with
      | val_clo x t3 => (t' = subst x v2 t3)
      | _ => False
      end
  end.

(* dependency lemma -- should be automatically generated *)
Lemma EvalRec_dep : captures_dep eval EvalOpt EvalRec.
Proof using.
  intros g Hg t t' HR E. unfolds EvalOpt, EvalRec.
  destruct t; try congruence.
  (* { false. } *)
  { lets (a&Ha&E2): Binds_not_None_inv (rm E). lets Ea: Hg Ha.
    lets (b&Hb&E3): Binds_not_None_inv (rm E2). lets Eb: Hg Hb.
    rewrite Eb in HR. case_if.
    { destruct HR as [|[|]]; try congruence. }
    { rewrite Ea in HR. destruct a; 
      destruct HR as [|[|]]; try congruence. } }
Qed.

(** Demo: computing with [EvalOpt] to derive a result of [eval].
    Here [100%nat] is an arbitrary, sufficiently large bound on the depth.
    Let's evaluation [((fun x -> x) (fun x -> x)) 3]. In concrete syntax:
    [trm_app (trm_app (id id) (val_nat 3)] where [id := trm_abs x (trm_var x)]
    evaluates to [val_nat 3] *)

Lemma evalAppIdId3 : 
  let x := 0%nat in (* an arbitrary identifier *)
  let id := trm_abs x (trm_var x) in
  let t := trm_app (trm_app id id) (val_nat 3) in
  exists r, eval t = r.
Proof using.
  exists. applys FixFun_eq_FixOpt 100%nat EvalOpt_simu EvalOpt_mono; [reflexivity|].
  cbv. (* evaluates [val_nat 3] *)
  reflexivity.
Qed.

(** Demo: computing [eval omega] which loops infinitely, where [omega] = [delta delta]
    and [delta = trm_abs x (trm_app x x)].
    Here [100%nat] is an arbitrary depth. After 100 calls, the function [EvalOpt]
    returns [None]. *)

Lemma evalOmega : 
  let x := 0%nat in (* an arbitrary identifier *)
  let delta := trm_abs x (trm_app (trm_var x) (trm_var x)) in
  let omega := trm_app delta delta in
  exists r, eval omega = r.
Proof using.
  exists. applys FixFun_eq_FixOpt 100%nat EvalOpt_simu EvalOpt_mono; [reflexivity|].
  cbv. (* produces the unprovable goal [None = Some ?r] *)
Abort.

(** Demo: proving a property of [eval], e.g. if [eval t] terminates on an 
    output value [v] which is not an error, then [big t v] holds, where [big] 
    denotes the standard big-step relation. *)

Inductive big : trm -> val -> Prop :=
  | big_val : forall v,
      v <> val_error ->
      big (trm_val v) v
  | big_abs : forall x t,
      big (trm_abs x t) (val_clo x t)
  | big_app : forall t1 t2 x t3 v2 v,
      big t1 (val_clo x t3) ->
      big t2 v2 ->
      big (subst x v2 t3) v ->
      big (trm_app t1 t2) v.

Lemma eval_big : forall t, terminates EvalOpt t -> 
    let v := eval t in
    v <> val_error ->
    big t v.
Proof using.
  intros t Ht.
  applys FixFun_fix_ter (fun t v => v <> val_error -> big t v) 
   EvalOpt_simu EvalOpt_mono EvalRec_dep; auto.
  clears t. intros t _ IH Ht. sets v: (Eval eval t).
  unfolds Eval. destruct t. 
  { subst v. constructor. auto. }
  { subst v. false. }
  { subst v. constructor. }
  { subst v. case_if. sets_eq v1: (eval t1). sets_eq v2: (eval t2).
     destruct v1; tryfalse. (* TODO: beautify proof case *)
     renames v to x, t to t3.
     applys big_app x t3 v2.
     { rewrite EQv1. applys IH.
       { hnf. eauto. }
       { congruence. } }
     { rewrite EQv2. applys IH.
       { hnf. eauto. }
       { unfolds is_error. destruct v2; congruence. } }
     { applys IH. 
        { hnf. right. intros. right. intros. subst v0. subst v2. case_if.
          subst v1. rewrite <- EQv1. auto. }
        { auto. } } } 
Qed.


(** Demo: proving a property of [eval], e.g. if [eval t] terminates on an 
    output value [v], possibly an error, then [bigx t v] holds, where [bigx] 
    denotes the standard big-step relation extended with error behaviors. *)

Definition is_closure (t:trm) : bool :=
  match t with
  | val_clo x t3 => true
  | _ => false
  end.

Inductive bigx : trm -> val -> Prop :=
  | bigx_val : forall v, (* including the case [v = val_error] *)
      bigx (trm_val v) v
  | bigx_abs : forall x t,
      bigx (trm_abs x t) (val_clo x t)
  | bigx_var : forall x,
      bigx (trm_var x) val_error
  | bigx_app : forall t1 t2 x t3 v2 v,
      bigx t1 (val_clo x t3) ->
      bigx t2 v2 ->
      bigx (subst x v2 t3) v ->
      bigx (trm_app t1 t2) v
  | bigx_app_err1 : forall t1 t2 v2 v1,
      bigx t2 v2 ->
      v2 <> val_error ->
      bigx t1 v1 ->
      ~ is_closure v1 ->
      bigx (trm_app t1 t2) val_error
  | bigx_app_err2 : forall t1 t2,
      bigx t2 val_error ->
      bigx (trm_app t1 t2) val_error.


Lemma eval_bigx : forall t, terminates EvalOpt t -> 
  let v := eval t in
  bigx t v.
Proof using.
  intros.
  applys FixFun_fix_ter (fun t v => bigx t v) 
   EvalOpt_simu EvalOpt_mono EvalRec_dep; auto.
  clears v t. intros t _ IH. sets v: (Eval eval t).
  unfolds Eval. destruct t. 
  { subst v. constructor. }
  { subst v. constructors. }
  { subst v. constructor. }
  { subst v. sets_eq v2: (eval t2). case_if. (* TODO: beautify this case *)
    { applys bigx_app_err2. destruct v2; tryfalse.
      rewrite EQv2. applys IH. { hnf. eauto. } }
    { sets_eq v1: (eval t1). tests: (is_closure v1).
      { destruct v1; tryfalse. renames v to x, t to t3.
        applys bigx_app x t3 v2.
        { rewrite EQv1. applys IH. { hnf. eauto. } }
        { rewrite EQv2. applys IH. { hnf. eauto. } }
        { applys IH. { hnf. right. intros. right. intros. subst v0. subst v2. case_if.
          subst v1. rewrite <- EQv1. auto. } } } 
      { asserts_rewrite (match v1 with
          | val_clo x t3 => eval (subst x v2 t3)
          | _ => val_error
          end = val_error). { destruct v1; unfolds is_closure; tryfalse; auto. } 
        applys bigx_app_err1 v2 v1.
        { rewrite EQv2. applys IH. { hnf. eauto. } }
        { unfolds is_error. destruct v2; congruence. }
        { rewrite EQv1. applys IH. { hnf. eauto. } }
        { unfolds is_error. destruct v1; congruence. } } } }
Qed.

End Evaluator.
































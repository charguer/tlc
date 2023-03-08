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

(*
Lemma iter_zero : forall A B (F:(A->B)->(A->B)) (f:A->B) (x:A),
  iter 0 F f x = f x.
Proof using. auto. Qed.

Lemma iter_succ : forall A B (F:(A->B)->(A->B)) (f:A->B) (n:nat) (x:A),
  iter (S n) F f x = F (iter n F f) x.
Proof using. auto. Qed.
*)
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

(** [FixOpt] takes a functional expressed in the error monad, and returns
    its fixed point expressed in the non-termination monad. *)

Definition FixOpt A B (Fopt:(A->option B)->(A->option B)) : nat->A->option B :=
  fix fopt (n:nat) (x:A) : option B :=
    match n with
    | O => None
    | S n' => Fopt (fopt n') x
    end.

(** [is_monadic_variant f g] asserts that [g] is a reformulation of the function [f]
    in the error monad (with respect to correctness only, not w.r.t. to completeness). *)

Definition is_monadic_variant A B (f : A -> B) (g : A -> option B) : Prop :=
  forall x z, g x = Some z -> f x = z.

(** [is_ho_monadic_variant F G] asserts that the functional [G] is a reformulation of 
    the functional [F], as a combinator in the error monad (again, w.r.t. correctness only). *)

Definition is_ho_monadic_variant A B
 (F : (A->B)->(A->B)) (Fopt : (A->option B)->(A->option B)) : Prop :=
  forall f fopt,
  is_monadic_variant f fopt ->
  is_monadic_variant (F f) (Fopt fopt).

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

(** [terminates G x] asserts that the function [FixOpt Fopt] returns a
    proper output on the input [x], meaning that its execution does not 
    run out of fuel. *)

Definition terminates A B (G:(A->option B)->(A->option B)) (x:A) : Prop :=
  exists n, FixOpt G n x <> None.

(** [captures_dep Fopt R] asserts that, for the functional [G] written in the
    error monad, the relation [R] describes (technically over-approximates)
    the recursive call graph: if a call on input [x] involves a recursive on input [y],
    then [R y x] holds. *)

Definition captures_dep A B (G:(A->option B)->(A->option B)) (R : A->A->Prop) : Prop :=
  forall h x y, R y x -> G h x <> None -> h y <> None. 

(** [captures_dep G R] guarantees in particular that, when [R y x] holds,
    [FixOpt Fopt (S n) x <> None] implies [FixOpt Fopt n y <> None]. *)

Lemma captures_dep_on_FixOpt : forall A B (G:(A->option B)->(A->option B)) (R : A->A->Prop),
  captures_dep G R -> 
  let fopt := FixOpt G in
  forall n x y, 
  R y x -> 
  fopt (S n) x <> None -> 
  fopt n y <> None.
Proof using. introv M HR HN. applys M HR HN. Qed.

Lemma FixOpt_eq_Some_inv_pos : forall A B (G:(A->option B)->(A->option B)) n x,
  FixOpt G n x <> None ->
  (n > 0)%nat.
Proof using. introv M. destruct n. { false* M. } { math. } Qed.

(** The following fixed point induction principle asserts that, on the domain of input
    values [x] on which [FixFun Fopt] terminates with a proper output, one can reason
    about behaviors of the fixed point by induction over the graph of recursive calls. *)

Lemma FixFun_fix_ter : forall A B {IB:Inhab B} f (F:(A->B)->(A->B)) (P:A->B->Prop)
   (G:(A->option B)->(A->option B)) (R:A->A->Prop),
  f = FixFun F ->
  is_ho_monadic_variant F G ->
  captures_dep G R ->
  (forall h x,
    (forall y, R y x -> P y (h y)) ->
    P x (F h x)) ->
  forall x, terminates G x -> P x (f x).
Proof using.
  introv Hf HG HR HI Hx. 
  destruct Hx as (n&Hx). case_eq (FixOpt G n x); [|auto_false]. intros y Hy.
  lets MG: iter_of_is_ho_monadic_variant (rm HG).
  asserts HFnx: (FixFun_iter_indep F n x).
  { intros g1 g2. rewrites (>> MG g1 Hy). rewrites* (>> MG g2 Hy). }
    (* alternative: { applys FixFun_iter_indep_of_image. intros g. rewrites* (>> MG g Hy). } *)
  asserts Ef: (f x = iter n F f x). skip. (* TODO *)
  rewrite Ef. clear Ef.
  lets Hn: FixOpt_eq_Some_inv_pos Hx.
  clear Hy HFnx y. gen Hn x. induction_wf IH: wf_lt n. intros Hn x Hx.
  destruct n as [| n']; [false;math|]. simpl. applys HI.
  intros y HRy. lets Hy: captures_dep_on_FixOpt HR HRy Hx.
  lets Hn': FixOpt_eq_Some_inv_pos Hy.
  applys IH Hy; try math.
Qed.




Lemma FixFun_fix_ter : forall A B {IB:Inhab B} f (F:(A->B)->(A->B)) (P:A->B->Prop)
   (Fopt:(A->option B)->(A->option B)) (R:A->A->Prop),
  f = FixFun F ->
  is_ho_monadic_variant F Fopt ->
  captures_dep Fopt R ->
  (forall h x,
    (forall y, R y x -> P y (h y)) ->
    P x (F h x)) ->
  forall x, terminates Fopt x -> P x (f x).
Proof using.
  forall g, iter n F g x = y.
  FixFun_iter_indep F n x ->
  forall g, f x = iter n F g x
  then induction n
Qed.

Definition maximal_dep A B (f g : (A->option B)) : (A->A->Prop) :=
  fun x y => f x <> None -> g y <> None.

Lemma FixFun_fix_ter_sat : forall A B (F:(A->B)->(A->B)) (P:A->B->Prop),
  f = FixFun F ->
  let fopt := FixOpt Fopt in
  (exists g, forall x, P x (g x)) ->
  is_ho_monadic_variant F Fopt ->
  (forall h x, (forall y, P y (h y)) -> P x (F h x)) ->
  forall x, terminates fopt x -> P x (f x).
Proof using.
  def fdep x y := forall n, fopt (S n) x <> None -> fopt n y <> None.
  def hxSn := fun y => if fdep x y then fopt n y else g y.
Qed.



(* ********************************************************************** *)
(* DEPRECATED


(** -------- Results for Terminating Evaluations --------- *)

(** [f] partial fixed point of [F] implies [f] partial fixed point of any
    iterate of [F], that is, [f x = iter n F f x]. *)

Lemma partial_fixed_point_iter :
   forall (A B : Type) (E : B -> B -> Prop),
   forall (F : (A -> B) -> A -> B) (f : A --> B) (n:nat),
  equiv E ->
  partial_fixed_point E F f ->
  partial_fixed_point E (iter n F) f.
Proof using.
  introv HE M. gen f. induction n; simpl.
  { intros g Hg x Dx. applys~ equiv_refl. }
  { intros g Hg x Dx. hnf in Hg.
    forwards K: IHn (Build_partial (iter n F g) (dom g)).

 skip. unfolds partial_fixed_point. unfolds fixed_point. hnf in K.

Qed.

  = (forall g, (forall x, P x -> f x = g x) -> forall x, P x -> g x = F g x).
Proof using. auto. Qed.




(** Specialized version of [FixFunMod_inv] *)
Lemma FixFunMod_inv' :
  forall A (P:A->Prop) B {IB:Inhab B} (F:(A->B)->(A->B)) (f:A->B),
  let fp := Build_partial f P in
  partial_fixed_point eq F fp ->
  (forall fp', partial_fixed_point eq F fp' -> consistent eq fp fp') ->
  (forall x, P x -> FixFun F x = f x).
Proof using.
  introv M1 M2 Px. symmetry. applys* FixFunMod_inv. split*.
Qed.

(** We let [Terminates F n] denote the set of input values [x] such that [F^n f x]
    does not depend on [f]. Intuitively, this corresponds to the set of input
    for which the recursive function described by the functional [F] terminates
    with maximal recursion depth [n]. Technically, the recursive function might
    not terminate in cornercases, such as when the return value of a recursive
    call is irrelevant to the final result. Examples include
    [let rec f (x : unit) = f x] and [let rec f x = ignore (f x)]. But in practice,
    as programmers, we are only interested in making recursive calls in cases
    where the value produced by that recursive call effectively matters to the
    final result. Therefore, for all practical applications, it makes sense
    to think of [Terminates F n] as characterized by termination at depth at most [n]. *)

Definition Terminates A B (F:(A->B)->(A->B)) (n:nat) : A -> Prop :=
  fun (x:A) => forall f1 f2, iter n F f1 x = iter n F f2 x.

(** The sets [Terminates F n] get larger as [n] grows. The limit of this series
    is the optimal fixed point. LATER: prove this limit theorem? *)

(** As we show next, given an arbitrary [f],
    the function [F^n f] is a partial fixed point on the domain [Terminates F n]
    for any n > 0. *)

(* Specialized def *)
Lemma partial_fixed_point_eq : forall (A B : Type) (F : (A -> B) -> A -> B) (P : A -> Prop) (f : A -> B),
    partial_fixed_point eq F (Build_partial f P)
  = (forall g, (forall x, P x -> f x = g x) -> forall x, P x -> g x = F g x).
Proof using. auto. Qed.
(*

Lemma Iter_partial_fixed_point :  forall A B (F:(A->B)->(A->B)) (n:nat) (f:A->B),
  n > 0%nat ->
  partial_fixed_point eq F (Build_partial (iter n F f) (Terminates F n)).
Proof.
  intros A B F n. induction n; intros. { false. math. }
  destruct n as [|n].
  { rewrite partial_fixed_point_eq. intros g Hg x Px.
    unfolds Terminates. simpls. rewrite <- Hg. applys Px. intros. applys Px. }
  { sets_eq m: (S n). rewrite partial_fixed_point_eq. intros g Hg x Px.
    forwards R: IHn f. math. rewrite partial_fixed_point_eq in R.
    rewrite~ <- Hg. simpl. unfolds in Px. simpl in Px.
    specializes R (iter m F f) __. applys Px.
rewrite Px.
Qed.

*)



(** Contraction property for [iter F n f_arbitrary] on the domain [Terminates F n] *)

(* ??
Lemma Terminates_contractive : forall A B (F:(A->B)->(A->B)) (n:nat) (f farb:A->B),
  f = iter n F farb ->
  forall x, Terminates F n x ->
  forall f1 f2,
  (forall y m, m < n -> Terminates F m y -> f1 y = f2 y) ->
  F f1 x = F f2 x.
Proof using.
  intros A B F n. induction n; introv Eqf Hx M.
  specializes Hx f1 f2. simpls.
Qed.
*)


FixFun_fix_partial



(** Because the function is contractive on its domain
    it follows that if [F^n f x] admits a value [y] that does not depend on [f],
    then the optimal fixed point maps [x] to [y], that is, [FixFun F x = y]. *)

Lemma FixFun_fix_iter_inv :
 forall A B {IB:Inhab B} (F:(A->B)->(A->B)) (f:A->B) (x:A) (y:B) (n:nat),
  f = FixFun F ->
  y = iter n F f x ->
  (forall f', iter n F f' x = y) ->
  f x = y.
Proof using.
 Admitted.



(** Auxiliary result for [FixFun_fix_iter_inv]: if [f] is an arbitrary fixed point
   of [F] on a domain [D], then for any [x] in that domain [D], we have [f x = F^n f x] *)
Lemma FixFun_iter_fix :
 forall A B (F:(A->B)->(A->B)) (D:A->Prop) (f:A->B) (x:A) (n:nat),
  D x ->
  (forall a, D a -> f a = F f a) ->
  f x = iter n F f x.
Proof using.
v  introv Dx Hf. set (g n a := If D a then f a else iter n F f a).
  cuts M: (forall n a, f a = iter n F f a).
  { specializes M n x. unfold g in M. case_if. apply M. }
  { clears n x. intro n. subst g. induction n; intros; case_if; simpl; auto.
    rewrite~ Hf. fequals. extens. intros b. specializes IHn b. case_if; auto.

  introv Dx Hf. set (g n a := If D a then f a else iter n F f a).
  cuts M: (forall n a, g n a = iter n F f a).
  { specializes M n x. unfold g in M. case_if. apply M. }
  { clears n x. intro n. subst g. induction n; intros; case_if; simpl; auto.
    rewrite~ Hf. fequals. extens. intros b. specializes IHn b. case_if; auto.
Qed.


(** If on an input [x] the value of [F^n f x] ion of the functional returns a result [y]
    that does not depend on the continuation [f], then [y] is the value of the optimal
    fixed point of [F] on that input. *)


(** If [FixFun_iter_indep F n x] holds, then the fixed point equation holds
    at [x]. *)

Lemma FixFun_iter_indep_fix : forall A B (F:(A->B)->(A->B)) (n:nat) (x:A),
  FixFun_iter_indep F n x ->
  forall g, iter n F g x = F (iter n F g) x.
Proof using. introv Hx. intros g. rewrite iter_swap. applys Hx. Qed.

(** As a corollary, if [FixFun_iter_indep F n x] holds, then the function
    [iter n F g] for an arbitrary [g] is a partial fixed point on the domain
    made of the singleton element [x]. *)

Lemma FixFun_iter_indep_partial_fixed_point : forall A B (F:(A->B)->(A->B)) (n:nat) (x:A),
  FixFun_iter_indep F n x ->
  forall g, partial_fixed_point eq F (Build_partial (iter n F g) (= x)).
Proof using.
  introv Hx. intros g. intros h Hh. simpls.
  unfolds pfun_equiv. intros ? ->.
  specializes Hh x __.
 
  asserts M: (h = iter n F g). { extens. intros y. rewrite* Hh.



 rewrite iter_swap. applys Hx. Qed.

Build_partial (iter n F g) (dom_singleton x) in
   eq F f.


(** If [FixFun_iter_indep F n x] holds, then [x] belongs to the domain
    of the optimal fixed point of [F], and [iter n F g] for an arbitrary [g]
    provides the image associated to [x] by the fixed point. *)

Lemma FixFun_iter_indep_fix : forall A B f (F:(A->B)->(A->B)) (n:nat) (x:A),
  f = FixFun F ->
  FixFun_iter_indep F n x ->
  forall g, f x = iter n F g x.
Proof using.
(*
   let h be another fixed point.
   by iter_partial_fixed_point we have:
   h x = iter n F h x.
   by FixFun_iter_indep
   iter n F h x = iter n F g x

exploit
Lemma FixFunMod_inv :
  forall A (P:A->Prop) B {IB:Inhab B} (F:(A->B)->(A->B)) (E:binary B) (f f':A->B),
  f = FixFunMod E F ->
  equiv E ->
  generally_consistent_partial_fixed_point E F (Build_partial f' P) ->
  pfun_equiv E P f' f.

to show that on the x, the intersection of the domains,

  let f := Build_partial (iter n F g) (dom_singleton x) in
  partial_fixed_point eq F f.
      by FixFun_iter_indep_fix.

*)
Qed.

(** [captures_dep f g R] asserts that the relation [R x y] ensures that
    if [f] . *)

Definition captures_dep A B (f g : (A->option B)) (R : A->A->Prop) : Prop :=
  forall x y, R y x -> f x <> None -> g y <> None.


Definition captures_dep A B (fopt : nat->A->option B) (R : A->A->Prop) : Prop :=
  forall n x y, R y x -> fopt (S n) x <> None -> fopt n y <> None.
*)
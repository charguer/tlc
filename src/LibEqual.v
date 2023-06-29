(**************************************************************************
* TLC: A library for Coq                                                  *
* Equality                                                                  *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics LibAxioms.
Generalizable Variables A.


(* ********************************************************************** *)
(** * Definition of equality *)

(* ---------------------------------------------------------------------- *)
(** ** Definition of Leibnitz' equality *)

(* Recall that the prelude defines equality [eq], with the notation
   [x = y] and [x = y :> A].
*)

Arguments eq {A}.

(* ---------------------------------------------------------------------- *)
(** ** Partial application of Leibnitz' equality *)

(** [= x] is a unary predicate which holds of values equal to [x].
    It simply denotes the partial application of equality.
    [= x :> A] allows to specify the type. *)

Notation "'=' x :> A" := (fun y => y = x :> A)
  (at level 71, x at next level).
Notation "'=' x" := (fun y => y = x)
  (at level 71).

(** [<> x] is a unary predicate which holds of values disequal to [x].
    It simply denotes the partial application of disequality.
    [<> x :> A] allows to specify the type. *)

Notation "'<>' x :> A" := (fun y => y <> x :> A)
  (at level 71, x at next level).
Notation "'<>' x" := (fun y => y <> x)
  (at level 71).


(* ---------------------------------------------------------------------- *)
(** ** Typeclass to exploit extensionality *)

(** The property [Extensionality A] captures the fact that the type [A]
    features an extensional equality, in the sense that to prove the
    equality between two values of type [A] it suffices to prove that
    those two values are related by some binary relation. *)

Class Extensionality (A:Type) := Extensionality_make {
  extensionality_hyp : A -> A -> Prop;
  extensionality : forall (x y : A), extensionality_hyp x y -> x = y }.

Arguments extensionality [A].
Arguments Extensionality_make [A] [extensionality_hyp].

(** Instance for propositional extensionality *)

Global Instance extensionatity_prop : Extensionality Prop.
Proof using. intros. apply (Extensionality_make prop_ext). Defined.


(* ---------------------------------------------------------------------- *)
(** ** Tactic to exploit extensionality *)

Ltac extens_reveal_eq tt :=
  match goal with
  | |- _ = _ => idtac
  | _ => first [ intro; extens_reveal_eq tt
               | fail 2 "extens needs hnf to reveal an equality" ]
  end.

Ltac extens_core tt :=
  extens_reveal_eq tt;
  applys extensionality;
  simpl extensionality_hyp.

Tactic Notation "extens" :=
  extens_core tt.
Tactic Notation "extens" "~" :=
  extens; auto_tilde.
Tactic Notation "extens" "*" :=
  extens; auto_star.


(* ********************************************************************** *)
(** * Properties of equality *)

(** This section contains a reformulation of the lemmas provided by
    the standard library concerning equality. *)

(* ---------------------------------------------------------------------- *)
(** ** Equality as an equivalence relation *)

(** See also sectin [Eq] from [LibRelation] for reformulation of theses
    results using high-level definitions. *)

Section EqualityProp.
Variables (A : Type).
Implicit Types x y z : A.

(** Reflexivity is captured by the constructor [eq_refl]. *)

(** Symmetry *)

Lemma eq_sym : forall x y,
  x = y ->
  y = x.
Proof using. introv H. destruct~ H. Qed.

(** Transitivity *)

Lemma eq_trans_ll : forall y x z,
  x = y ->
  y = z ->
  x = z.
Proof using. introv H1 H2. destruct~ H2. Qed.

Definition eq_trans := eq_trans_ll.

Lemma eq_trans_lr : forall y x z,
  x = y ->
  z = y ->
  x = z.
Proof using. introv H1 H2. destruct~ H2. Qed.

Lemma eq_trans_rl : forall y x z,
  y = x ->
  y = z ->
  x = z.
Proof using. introv H1 H2. destruct~ H2. Qed.

Lemma eq_trans_rr : forall y x z,
  y = x ->
  z = y ->
  x = z.
Proof using. introv H1 H2. destruct~ H2. Qed.

End EqualityProp.

Arguments eq_trans_ll [A].
Arguments eq_trans_lr [A].
Arguments eq_trans_rl [A].
Arguments eq_trans_rr [A].
Arguments eq_trans [A].


(* ---------------------------------------------------------------------- *)
(** ** Properties of disequality *)

Section DisequalityProp.
Variables (A : Type).
Implicit Types x y : A.

(** Symmetry *)

Lemma neq_sym : forall x y,
  x <> y ->
  y <> x.
Proof using. introv H K. destruct~ K. Qed.

End DisequalityProp.


(* ---------------------------------------------------------------------- *)
(** ** Symmetrized induction principles *)

(* Remark: it is not clear if these results are any useful in practice. *)

Section EqInductionSym.
Variables (A : Type) (x : A).

Definition eq_ind_r : forall (P:A -> Prop),
  P x -> forall y, y = x -> P y.
Proof using. intros. subst*. Qed.

Definition eq_rec_r : forall (P:A -> Set),
  P x -> forall y, y = x -> P y.
Proof using. intros. subst*. Qed.

Definition eq_rect_r : forall (P:A -> Type),
  P x -> forall y, y = x -> P y.
Proof using. intros. subst*. Qed.

End EqInductionSym.



(* ********************************************************************** *)
(** * Functional extensionality *)

(* ---------------------------------------------------------------------- *)
(** ** Dependent functional extensionality *)

Section FuncExtDep.
Variables (A1 : Type).
Variables (A2 : forall (x1 : A1), Type).
Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).
Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).
Variables (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type).
Variables (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

Lemma fun_ext_1 : forall (f g : forall (x1:A1), A2 x1),
  (forall x1, f x1 = g x1) ->
  f = g.
Proof using. repeat (intros; apply fun_ext_dep). auto. Qed.

Lemma fun_ext_2 : forall (f g : forall (x1:A1) (x2:A2 x1), A3 x2),
  (forall x1 x2, f x1 x2 = g x1 x2) ->
  f = g.
Proof using. repeat (intros; apply fun_ext_dep). auto. Qed.

Lemma fun_ext_3 : forall (f g : forall (x1:A1) (x2:A2 x1) (x3:A3 x2), A4 x3),
  (forall x1 x2 x3, f x1 x2 x3 = g x1 x2 x3) ->
  f = g.
Proof using. repeat (intros; apply fun_ext_dep). auto. Qed.

Lemma fun_ext_4 : forall (f g: forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
  (x4:A4 x3), A5 x4),
  (forall x1 x2 x3 x4, f x1 x2 x3 x4 = g x1 x2 x3 x4) ->
  f = g.
Proof using. repeat (intros; apply fun_ext_dep). auto. Qed.

Lemma fun_ext_5 : forall (f g: forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
  (x4:A4 x3) (x5:A5 x4), A6 x5),
  (forall x1 x2 x3 x4 x5, f x1 x2 x3 x4 x5 = g x1 x2 x3 x4 x5) ->
  f = g.
Proof using. repeat (intros; apply fun_ext_dep). auto. Qed.

Global Instance Extensionality_fun_1 :
  Extensionality (forall (x1:A1), A2 x1).
Proof using. intros. apply (Extensionality_make fun_ext_1). Defined.

Global Instance Extensionality_fun_2 :
  Extensionality (forall (x1:A1) (x2:A2 x1), A3 x2).
Proof using. intros. apply (Extensionality_make fun_ext_2). Defined.

Global Instance Extensionality_fun_3 :
  Extensionality (forall (x1:A1) (x2:A2 x1) (x3:A3 x2), A4 x3).
Proof using. intros. apply (Extensionality_make fun_ext_3). Defined.

Global Instance Extensionality_fun_4 :
  Extensionality (forall (x1:A1) (x2:A2 x1) (x3:A3 x2) (x4:A4 x3), A5 x4).
Proof using. intros. apply (Extensionality_make fun_ext_4). Defined.

Global Instance Extensionality_fun_5 :
  Extensionality (forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
  (x4:A4 x3) (x5:A5 x4), A6 x5).
Proof using. intros. apply (Extensionality_make fun_ext_5). Defined.

Lemma fun_eta_dep_1 : forall (f : forall (x1:A1), A2 x1),
  (fun x1 => f x1) = f.
Proof using. intros. apply~ fun_ext_1. Qed.

Lemma fun_eta_dep_2 : forall (f : forall (x1:A1) (x2:A2 x1), A3 x2),
  (fun x1 x2 => f x1 x2) = f.
Proof using. intros. apply~ fun_ext_2. Qed.

Lemma fun_eta_dep_3 : forall (f : forall (x1:A1) (x2:A2 x1) (x3:A3 x2), A4 x3),
  (fun x1 x2 x3 => f x1 x2 x3) = f.
Proof using. intros. apply~ fun_ext_3. Qed.

Lemma fun_eta_dep_4 : forall (f : forall (x1:A1) (x2:A2 x1) (x3:A3 x2) (x4:A4 x3), A5 x4),
  (fun x1 x2 x3 x4 => f x1 x2 x3 x4) = f.
Proof using. intros. apply~ fun_ext_4. Qed.

Lemma fun_eta_dep_5 : forall (f : forall (x1:A1) (x2:A2 x1) (x3:A3 x2) (x4:A4 x3) (x5:A5 x4), A6 x5),
  (fun x1 x2 x3 x4 x5 => f x1 x2 x3 x4 x5) = f.
Proof using. intros. apply~ fun_ext_5. Qed.

End FuncExtDep.


(* ---------------------------------------------------------------------- *)
(** ** Non-dependent functional extensionality *)

(* Remark: are these lemmas really useful, given that they are subsumed
   by their more general versions above? Probably could do without. *)

Lemma fun_ext_nondep_1 : forall A1 B (f g : A1 -> B),
  (forall x1, f x1 = g x1) ->
  f = g.
Proof using. intros. apply~ fun_ext_1. Qed.

Lemma fun_ext_nondep_2 : forall A1 A2 B (f g : A1 -> A2 -> B),
  (forall x1 x2, f x1 x2 = g x1 x2) ->
  f = g.
Proof using. intros. apply~ fun_ext_2. Qed.

Lemma fun_ext_nondep_3 : forall A1 A2 A3 B (f g : A1 -> A2 -> A3 -> B),
  (forall x1 x2 x3, f x1 x2 x3 = g x1 x2 x3) ->
  f = g.
Proof using. intros. apply~ fun_ext_3. Qed.

Lemma fun_ext_nondep_4 : forall A1 A2 A3 A4 B (f g : A1 -> A2 -> A3 -> A4 -> B),
  (forall x1 x2 x3 x4, f x1 x2 x3 x4 = g x1 x2 x3 x4) ->
  f = g.
Proof using. intros. apply~ fun_ext_4. Qed.

Lemma fun_ext_nondep_5 : forall A1 A2 A3 A4 A5 B (f g : A1 -> A2 -> A3 -> A4 -> A5 -> B),
  (forall x1 x2 x3 x4 x5, f x1 x2 x3 x4 x5 = g x1 x2 x3 x4 x5) ->
  f = g.
Proof using. intros. apply~ fun_ext_5. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Eta-conversion *)

Lemma fun_eta_1 : forall A1 B (f : A1 -> B),
  (fun x1 => f x1) = f.
Proof using. intros. apply~ fun_ext_1. Qed.

Lemma fun_eta_2 : forall A1 A2 B (f : A1 -> A2 -> B),
  (fun x1 x2 => f x1 x2) = f.
Proof using. intros. apply~ fun_ext_2. Qed.

Lemma fun_eta_3 : forall A1 A2 A3 B (f : A1 -> A2 -> A3 -> B),
  (fun x1 x2 x3 => f x1 x2 x3) = f.
Proof using. intros. apply~ fun_ext_3. Qed.

Lemma fun_eta_4 : forall A1 A2 A3 A4 B (f : A1 -> A2 -> A3 -> A4 -> B),
  (fun x1 x2 x3 x4 => f x1 x2 x3 x4) = f.
Proof using. intros. apply~ fun_ext_4. Qed.

Lemma fun_eta_5 : forall A1 A2 A3 A4 A5 B (f : A1 -> A2 -> A3 -> A4 -> A5 -> B),
  (fun x1 x2 x3 x4 x5 => f x1 x2 x3 x4 x5) = f.
Proof using. intros. apply~ fun_ext_4. Qed.

#[global]
Hint Rewrite fun_eta_1 fun_eta_2 fun_eta_3 fun_eta_4 fun_eta_5 : rew_eta.



(* ********************************************************************** *)
(** * Predicate extensionality *)

(* ---------------------------------------------------------------------- *)
(** ** Dependend predicates *)

Section PropExt.
Variables (A1 : Type).
Variables (A2 : forall (x1 : A1), Type).
Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).
Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).
Variables (A5 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type).
Variables (A6 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

Lemma pred_ext_1 : forall (P Q : forall (x1:A1), Prop),
  (forall x1, P x1 <-> Q x1) ->
  P = Q.
Proof using. repeat (intros; apply fun_ext_dep). intros. apply~ prop_ext. Qed.

Lemma pred_ext_2 : forall (P Q : forall (x1:A1) (x2:A2 x1), Prop),
  (forall x1 x2, P x1 x2 <-> Q x1 x2) ->
  P = Q.
Proof using. repeat (intros; apply fun_ext_dep). intros. apply~ prop_ext. Qed.

Lemma pred_ext_3 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2), Prop),
  (forall x1 x2 x3, P x1 x2 x3 <-> Q x1 x2 x3) ->
  P = Q.
Proof using. repeat (intros; apply fun_ext_dep). intros. apply~ prop_ext. Qed.

Lemma pred_ext_4 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
  (x4:A4 x3), Prop),
  (forall x1 x2 x3 x4, P x1 x2 x3 x4 <-> Q x1 x2 x3 x4) ->
  P = Q.
Proof using. repeat (intros; apply fun_ext_dep). intros. apply~ prop_ext. Qed.

Lemma pred_ext_5 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
  (x4:A4 x3) (x5:A5 x4), Prop),
  (forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 <-> Q x1 x2 x3 x4 x5) ->
  P = Q.
Proof using. repeat (intros; apply fun_ext_dep). intros. apply~ prop_ext. Qed.

Lemma pred_ext_6 : forall (P Q : forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
  (x4:A4 x3) (x5:A5 x4) (x6:A6 x5), Prop),
  (forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 <-> Q x1 x2 x3 x4 x5 x6) ->
  P = Q.
Proof using. repeat (intros; apply fun_ext_dep). intros. apply~ prop_ext. Qed.

Global Instance Extensionality_pred_1 :
  Extensionality (forall (x1:A1), Prop).
Proof using. intros. apply (Extensionality_make pred_ext_1). Defined.

Global Instance Extensionality_pred_2 :
  Extensionality (forall (x1:A1) (x2:A2 x1), Prop).
Proof using. intros. apply (Extensionality_make pred_ext_2). Defined.

Global Instance Extensionality_pred_3 :
  Extensionality (forall (x1:A1) (x2:A2 x1) (x3:A3 x2), Prop).
Proof using. intros. apply (Extensionality_make pred_ext_3). Defined.

Global Instance Extensionality_pred_4 :
  Extensionality (forall (x1:A1) (x2:A2 x1) (x3:A3 x2) (x4:A4 x3), Prop).
Proof using. intros. apply (Extensionality_make pred_ext_4). Defined.

Global Instance Extensionality_pred_5 :
  Extensionality (forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
  (x4:A4 x3) (x5:A5 x4), Prop).
Proof using. intros. apply (Extensionality_make pred_ext_5). Defined.

Global Instance Extensionality_pred_6 :
  Extensionality (forall (x1:A1) (x2:A2 x1) (x3:A3 x2)
  (x4:A4 x3) (x5:A5 x4) (x6:A6 x5), Prop).
Proof using. intros. apply (Extensionality_make pred_ext_6). Defined.

End PropExt.


(* ---------------------------------------------------------------------- *)
(** ** Non-dependend predicate extensionality *)

(* Remark: are these lemmas really useful, given that they are subsumed
   by their more general versions above? Probably could do without. *)

Lemma pred_ext_nondep_1 :
  forall A1 (P Q : A1 -> Prop),
  (forall x1, P x1 <-> Q x1) ->
  P = Q.
Proof using. intros. apply~ pred_ext_1. Qed.

Lemma pred_ext_nondep_2 :
  forall A1 A2 (P Q : A1 -> A2 -> Prop),
  (forall x1 x2, P x1 x2 <-> Q x1 x2) ->
  P = Q.
Proof using. intros. apply~ pred_ext_2. Qed.

Lemma pred_ext_nondep_3 :
  forall A1 A2 A3 (P Q : A1 -> A2 -> A3 -> Prop),
  (forall x1 x2 x3, P x1 x2 x3 <-> Q x1 x2 x3) ->
  P = Q.
Proof using. intros. apply~ pred_ext_3. Qed.

Lemma pred_ext_nondep_4 :
  forall A1 A2 A3 A4 (P Q : A1 -> A2 -> A3 -> A4 -> Prop),
  (forall x1 x2 x3 x4, P x1 x2 x3 x4 <-> Q x1 x2 x3 x4) ->
  P = Q.
Proof using. intros. apply~ pred_ext_4. Qed.

Lemma pred_ext_nondep_5 :
  forall A1 A2 A3 A4 A5 (P Q : A1 -> A2 -> A3 -> A4 -> A5 -> Prop),
  (forall x1 x2 x3 x4 x5, P x1 x2 x3 x4 x5 <-> Q x1 x2 x3 x4 x5) ->
  P = Q.
Proof using. intros. apply~ pred_ext_5. Qed.

Lemma pred_ext_nondep_6 :
  forall A1 A2 A3 A4 A5 A6 (P Q : A1 -> A2 -> A3 -> A4 -> A5 -> A6 -> Prop),
  (forall x1 x2 x3 x4 x5 x6, P x1 x2 x3 x4 x5 x6 <-> Q x1 x2 x3 x4 x5 x6)  ->
  P = Q.
Proof using. intros. apply~ pred_ext_6. Qed.



(* ********************************************************************** *)
(** * Equality of function and predicate applications *)

(* --TODO: generalize this section to dependent arguments *)

(* ---------------------------------------------------------------------- *)
(** ** A same function applied to equal arguments yield equal result *)

Section ArgsEq.
Variables (A1 A2 A3 A4 A5 B : Type).

Lemma args_eq_1 : forall (f:A1->B) x1 y1,
  x1 = y1 ->
  f x1 = f y1.
Proof using. intros. subst~. Qed.

Lemma args_eq_2 : forall (f:A1->A2->B) x1 y1 x2 y2,
  x1 = y1 ->
  x2 = y2 ->
  f x1 x2 = f y1 y2.
Proof using. intros. subst~. Qed.

Lemma args_eq_3 : forall (f:A1->A2->A3->B) x1 y1 x2 y2 x3 y3,
  x1 = y1 ->
  x2 = y2 ->
  x3 = y3 ->
  f x1 x2 x3 = f y1 y2 y3.
Proof using. intros. subst~. Qed.

Lemma args_eq_4 : forall (f:A1->A2->A3->A4->B) x1 y1 x2 y2 x3 y3 x4 y4,
  x1 = y1 ->
  x2 = y2 ->
  x3 = y3 ->
  x4 = y4 ->
  f x1 x2 x3 x4 = f y1 y2 y3 y4.
Proof using. intros. subst~. Qed.

Lemma args_eq_5 : forall (f:A1->A2->A3->A4->A5->B) x1 y1 x2 y2 x3 y3 x4 y4 x5 y5,
  x1 = y1 ->
  x2 = y2 ->
  x3 = y3 ->
  x4 = y4 ->
  x5 = y5 ->
  f x1 x2 x3 x4 x5 = f y1 y2 y3 y4 y5.
Proof using. intros. subst~. Qed.

End ArgsEq.


(* ---------------------------------------------------------------------- *)
(** ** Equal functions applied to same arguments return equal results *)

(** These results are exploited by tactic [fequals] (see LibTactics);
    however the lemmas remain useful for forward-reasoning. *)

Section FuncEq.
Variables (A1 A2 A3 A4 A5 B:Type).
Variables (x1:A1) (x2:A2) (x3:A3) (x4:A4) (x5:A5).

Lemma fun_eq_1 : forall f g,
  f = g ->
  f x1 = g x1 :> B.
Proof using. intros. subst~. Qed.

Lemma fun_eq_2 : forall f g,
  f = g ->
  f x1 x2 = g x1 x2 :> B.
Proof using. intros. subst~. Qed.

Lemma fun_eq_3 : forall f g,
  f = g ->
  f x1 x2 x3 = g x1 x2 x3 :> B.
Proof using. intros. subst~. Qed.

Lemma fun_eq_4 : forall f g,
  f = g ->
  f x1 x2 x3 x4 = g x1 x2 x3 x4 :> B.
Proof using. intros. subst~. Qed.

Lemma fun_eq_5 : forall f g,
  f = g ->
  f x1 x2 x3 x4 x5 = g x1 x2 x3 x4 x5 :> B.
Proof using. intros. subst~. Qed.

End FuncEq.


(* ---------------------------------------------------------------------- *)
(** ** Equal predicates applied to same arguments return equivalent results *)

(** These results are exploited by tactic [fequals] (see LibTactics);
    however the lemmas remain useful for forward-reasoning. *)

Section PredEq.
Variables (A1 A2 A3 A4 A5 B:Type).
Variables (x1:A1) (x2:A2) (x3:A3) (x4:A4) (x5:A5).

Lemma pred_eq_1 : forall P Q,
  P = Q ->
  P x1 <-> Q x1.
Proof using. intros. subst*. Qed.

Lemma pred_eq_2 : forall P Q,
  P = Q ->
  P x1 x2 <-> Q x1 x2.
Proof using. intros. subst*. Qed.

Lemma pred_eq_3 : forall P Q,
  P = Q ->
  P x1 x2 x3 <-> Q x1 x2 x3.
Proof using. intros. subst*. Qed.

Lemma pred_eq_4 : forall P Q,
  P = Q ->
  P x1 x2 x3 x4 <-> Q x1 x2 x3 x4.
Proof using. intros. subst*. Qed.

Lemma pred_eq_5 : forall P Q,
  P = Q ->
  P x1 x2 x3 x4 x5 <-> Q x1 x2 x3 x4 x5.
Proof using. intros. subst*. Qed.

End PredEq.



(* ********************************************************************** *)
(** * Proof Irrelevance *)

(** The proof irrelevance lemma states that two proofs of a same
    proposition are always equal.
      [forall (P : Prop) (p q : P), p = q]
   This result is a consequence of propositional extensionality.
*)

(* ---------------------------------------------------------------------- *)
(** ** Proof of the proof-irrelevance result *)

Module PIfromExt.

Implicit Types P : Prop.

(** First, we prove that on an inhabited proposition type,
    there exists a fixpoint combinator. *)

Lemma prop_eq_self_impl_when_true : forall P,
  P ->
  P = (P -> P).
Proof using. intros. apply* prop_ext. Qed.

Record has_fixpoint (P:Prop) : Prop := has_fixpoint_make
  { has_fixpoint_F : (P -> P) -> P;
    has_fixpoint_fix : forall f, has_fixpoint_F f = f (has_fixpoint_F f) }.

Lemma prop_has_fixpoint_when_true : forall P,
  P ->
  has_fixpoint P.
Proof using.
  intros P a. set (P' := P).
  set (g1 := id : P' -> P). set (g2 := id : P -> P').
  asserts~ Fix: (forall x, g1 (g2 x) = x).
  clearbody g1 g2. gen g1 g2.
  rewrite (prop_eq_self_impl_when_true a).
  subst P'. intros.
  set (Y := fun f => (fun x => f (g1 x x)) (g2 (fun x => f (g1 x x)))).
  applys (has_fixpoint_make Y). (* --TODO: why [applys has_fixpoint_make Y] fails *)
  { intros f. unfold Y at 1. rewrite~ Fix. }
Qed.

(** We exploit the fixpoint combinator on the negation function, applied
    to the following special proposition type (isomorphic to booleans,
    but living in Prop). *)

Inductive boolP : Prop :=
  | trueP : boolP
  | falseP : boolP.

Lemma trueP_eq_falseP : trueP = falseP.
Proof using.
  lets (Y&Yfix): (@prop_has_fixpoint_when_true boolP trueP).
  set (neg := fun b => match b with| trueP => falseP | falseP => trueP end).
  lets F: ((rm Yfix) neg).
  set (b := Y neg).
  asserts~ E: (b = Y neg).
  destruct b.
  { change (trueP = neg trueP) in |- *. rewrite E. rewrite~ <- F. }
  { change (neg falseP = falseP) in |- *. rewrite E. rewrite~ <- F. }
Qed.

(** We now have two distinct constructors [trueP] and [falseP],
    which we can distinguish in the logic using [match] for
    any goal concluding on a proposition; and, at the same time,
    these two constructors are provably equal. We can exploit
    these properties to prove that two proofs of a same theorem
    are equal. *)

Lemma proof_irrelevance :
  forall (P : Prop) (p q : P), p = q.
Proof using.
  intros P p q.
  set (f := fun b => match b with | trueP => p | falseP => q end).
  change p with (f trueP).
  change q with (f falseP).
  rewrite~ trueP_eq_falseP.
Qed.

End PIfromExt.

Lemma proof_irrelevance : forall (P : Prop) (p q : P), p = q.
Proof using. exact PIfromExt.proof_irrelevance. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Consequences of proof irrelevance *)

(** Uniqueness of identity proofs *)

Lemma identity_proofs_unique :
  forall (A : Type) (x y : A) (p q : x = y),
  p = q.
Proof using. intros. apply proof_irrelevance. Qed.

(** Uniqueness of reflexive identity proofs (special case) *)

Lemma reflexive_identity_proofs_unique :
  forall (A : Type) (x : A) (p : x = x),
  p = refl_equal x.
Proof using. intros. applys identity_proofs_unique. Qed.

(** Invariance by substitution of reflexive equality proofs *)

Lemma eq_rect_refl_eq :
  forall (A : Type) (p : A) (Q : A -> Type) (x : Q p) (h : p = p),
  eq_rect p Q x p h = x.
Proof using. intros. rewrite~ (reflexive_identity_proofs_unique h). Qed.

(** Streicher's axiom K *)

Lemma streicher_K :
  forall (A : Type) (x : A) (P : x = x -> Prop),
  P (refl_equal x) ->
  forall (p : x = x), P p.
Proof using. intros. rewrite~ (reflexive_identity_proofs_unique p). Qed.

(** Coercion for rewriting a type equality in a term *)

Definition rewrite_type (A B:Type) (E:A=B) (V:A) : B :=
  eq_rect A (fun T => T) V B E.

Lemma rewrite_type_self : forall A (E:A=A) (V:A),
  rewrite_type E V = V.
Proof using. intros. unfold rewrite_type. rewrite* eq_rect_refl_eq. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Injectivity of equality on dependent pairs *)

(** This section establishes that [existT P p x = existT P p y] implies
    that [x] is equal to [y]. It indirectly results from the proof
    irrelevance property. *)

(** Definition of dependent equality, with non-dependent return type *)

Inductive eq_dep_nd (A : Type) (P : A -> Type)
    (p : A) (x : P p) (q : A) (y : P q) : Prop :=
 | eq_dep_nd_intro : forall (h : q = p),
    x = eq_rect q P y p h -> eq_dep_nd P p x q y.

Arguments eq_dep_nd [A] [P] [p] x [q] y.
Arguments eq_dep_nd_intro [A] [P] [p] [x] [q] [y].

(** Reflexivity of [eq_dep_nd] *)

Lemma eq_dep_nd_refl : forall (A : Type) (P : A -> Type) (p : A) (x : P p),
  eq_dep_nd x x.
Proof using. intros. apply (eq_dep_nd_intro (refl_equal p)). auto. Qed.

(** Injectivity of [eq_dep_nd] *)

Lemma eq_dep_nd_same_inv :
  forall (A : Type) (P : A -> Type) (p : A) (x y : P p),
  eq_dep_nd x y ->
  x = y.
Proof using. introv H. inversions H. rewrite~ eq_rect_refl_eq. Qed.

(** Equality on dependent pairs implies [eq_dep_nd] *)

Lemma eq_existT_inv :
  forall (A : Type) (P : A -> Type) (p q : A) (x : P p) (y : P q),
  existT P p x = existT P q y ->
  eq_dep_nd x y.
Proof using. introv E. dependent rewrite E. simpl. apply eq_dep_nd_refl. Qed.

(** Injectivity of equality on dependent pairs *)

Lemma eq_existT_same_inv :
  forall (A : Type) (P : A -> Type) (p : A) (x y : P p),
  existT P p x = existT P p y ->
  x = y.
Proof using. intros. apply eq_dep_nd_same_inv. apply~ eq_existT_inv. Qed.

(** Reformulated as an equality *)

Lemma eq_existT_same_eq :
  forall (A : Type) (P : A -> Type) (p : A) (x y : P p),
  (existT P p x = existT P p y) = (x = y).
Proof using.
  extens. iff M.
  { apply eq_dep_nd_same_inv. apply~ eq_existT_inv. }
  { subst*. }
Qed.


(* ---------------------------------------------------------------------- *)
(** Irrelevance of the membership property for subsets types *)

(** This is another consequence of proof irrelevance *)

Scheme eq_indd := Induction for eq Sort Prop.

Lemma exist_eq_exist : forall (A:Type) (P : A->Prop) (x y : A) (p : P x) (q : P y),
  x = y ->
  exist P x p = exist P y q.
Proof using.
  intros. rewrite (proof_irrelevance q (eq_rect x P p y H)). subst*.
Qed.

Lemma existT_eq_existT : forall (A:Type) (P:A->Prop) (x y:A) (p:P x) (q:P y),
  x = y ->
  existT P x p = existT P y q.
Proof using.
  intros. rewrite (proof_irrelevance q (eq_rect x P p y H)). subst*.
Qed.

Ltac fequal_support_for_exist tt ::= (* original in LibTactics *)
  first [ apply exist_eq_exist | apply existT_eq_existT ].


(* ********************************************************************** *)
(** * Dependent equality *)

(** In this section, we prove that [eq_dep x y] implies [x = y]. *)

(** Definition of [eq_dep] (copied from the Prelude) *)

Inductive eq_dep (A : Type) (P : A -> Type) (p : A) (x : P p)
  : forall q, P q -> Prop :=
  | eq_dep_refl : eq_dep P p x p x.

Arguments eq_dep [A] [P] [p] x [q].

(** Symmetry of [eq_dep] *)

Lemma eq_dep_sym : forall (A : Type) (P : A -> Type)
 (p q : A) (x : P p) (y : P q),
  eq_dep x y ->
  eq_dep y x.
Proof using. introv E. destruct E. constructor. Qed.

(** Transitivity of [eq_dep] *)

Lemma eq_dep_trans : forall (A : Type) (P : A -> Type)
 (p q r : A) (y : P q) (x : P p) (z : P r),
  eq_dep x y ->
  eq_dep y z ->
  eq_dep x z.
Proof using. introv E F. destruct~ E. Qed.

(** Proof of equivalence between [eq_dep_nd] and [eq_dep] *)

Scheme eq_induction := Induction for eq Sort Prop.

Lemma eq_dep_of_eq_dep_nd :
  forall (A : Type) (P : A -> Type) (p q : A) (x : P p) (y : P q),
  eq_dep_nd x y ->
  eq_dep x y.
Proof using.
  introv E. destruct E as (h,H).
  destruct h using eq_induction. subst~. constructor.
Qed.

Lemma eq_dep_nd_of_eq_dep :
  forall (A : Type) (P : A -> Type) (p q : A) (x : P p) (y : P q),
  eq_dep x y ->
  eq_dep_nd x y.
Proof using. introv H. destruct H. apply (eq_dep_nd_intro (refl_equal p)); auto. Qed.

(** Injectivity of dependent equality *)

Lemma eq_dep_same_inv :
  forall (A : Type) (P : A -> Type) (p : A) (x y : P p),
  eq_dep x y ->
  x = y.
Proof using.
  introv R. inversion R. apply eq_dep_nd_same_inv. apply~ eq_dep_nd_of_eq_dep.
Qed.

(** Equality on dependent pairs implies dependent equality *)

Lemma eq_dep_of_eq_existT :
  forall (A : Type) (P : A -> Type) (p q : A) (x : P p) (y : P q),
  existT P p x = existT P q y ->
  eq_dep x y.
Proof using. introv E. dependent rewrite E. simple~. constructor. Qed.


(* ********************************************************************** *)
(** * John Major's equality *)

Require Import Coq.Logic.JMeq.

(** The module above defines John Major's equality:

  Inductive JMeq (A : Type) (x : A) : forall B : Type, B -> Prop :=
     | JMeq_refl : JMeq x x.
*)

(** In this section, we prove that [JMeq x y] implies [x = y]
    when [x] and [y] have the same type. *)

(** Symmetry, transitivity of [JMeq] *)

Lemma JMeq_sym : forall (A B : Type) (x : A) (y : B),
  JMeq x y ->
  JMeq y x.
Proof using. introv E. destruct~ E. Qed.

Lemma JMeq_trans : forall (A B C : Type) (y : B) (x : A) (z : C),
  JMeq x y ->
  JMeq y z ->
  JMeq x z.
Proof using. introv E F. destruct~ E. Qed.

Local Hint Immediate JMeq_sym.

(** Relation between [JMeq] and [eq_dep] *)

Lemma eq_dep_of_JMeq : forall (A B : Type) (x : A) (y : B),
  JMeq x y ->
  @eq_dep Type (fun T => T) A x B y.
Proof using. introv E. destruct E. constructor. Qed.

Lemma JMeq_of_eq_dep : forall (A B : Type) (x : A) (y : B),
  @eq_dep Type (fun T => T) A x B y ->
  JMeq x y.
Proof using. introv E. destruct~ E. Qed.

(** Injectivity of [JMeq] *)

Lemma JMeq_same_inv : forall (A : Type) (x y : A),
  JMeq x y ->
  x = y.
Proof using.
  introv E. apply (@eq_dep_same_inv Type (fun T => T)).
  apply~ eq_dep_of_JMeq.
Qed.


(**************************************************************************
* TLC: A library for Coq                                                  *
* Well-founded relations                                                  *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics LibLogic
 LibProd LibSum LibRelation LibNat LibInt.


(* ********************************************************************** *)
(** * Compatibility *)

(** Coq's stdlib Prelude defines:

 Inductive Acc A (R:A->A->Prop) (x:A) : Prop :=
   | Acc_intro : (forall (y:A), R y x -> Acc y) -> Acc x.

 Definition well_founded A (R:A->A->Prop) :=
    forall (x:A), Acc x.

*)

(** TLC introduces [wf] as a shorter name for [well_founded], both
    for conciseness and for tactics to specifically recognize
    this symbol. *)

Definition wf := well_founded.


(* ---------------------------------------------------------------------- *)
(** ** Tactics *)

(** [auto with wf] attempts to unfold the names of
    the relations given as argument to [wf]. *)

#[global]
Hint Extern 1 (wf ?R) => progress (unfold R) : wf.

(** [solve_wf] is a shorthand for solving goals using
    [auto with wf], aimed to prove goals of the form [wf R]. *)

Tactic Notation "solve_wf" :=
  solve [ auto with wf ].



(* ********************************************************************** *)
(* * Measures *)

(* ---------------------------------------------------------------------- *)
(** ** Definition *)

(** [measure f] is a well-founded binary relation which
    relates [x] to [y] when [f x < f y], at type [nat]. *)

Definition measure A (f:A->nat) : binary A :=
  fun x1 x2 => (f x1 < f x2).


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Section Measure.
Variables (A : Type).
Implicit Type f : A -> nat.

Lemma wf_measure : forall f,
  wf (measure f).
Proof using.
  intros f a. gen_eq n: (f a). gen a. pattern n.
  apply peano_induction. clear n. introv IH Eq.
  apply Acc_intro. introv H. unfolds in H.
  rewrite <- Eq in H. apply* IH.
Qed.

Lemma trans_measure : forall (f : A -> nat),
  trans (measure f).
Proof using. intros. unfold measure, trans. intros. nat_math. Qed.

(* -- LATER: Lemma order_measure *)

End Measure.

#[global]
Hint Resolve wf_measure : wf.


(* ---------------------------------------------------------------------- *)
(** ** Measure on pairs *)

Definition measure2 A1 A2 (f : A1 -> A2 -> nat) : binary (A1*A2) :=
  fun p1 p2 => let (x1,y1) := p1 in
               let (x2,y2) := p2 in
               (f x1 y1 < f x2 y2).

Lemma wf_measure2 : forall A1 A2 (f:A1->A2->nat),
  wf (measure2 f).
Proof using.
  intros A1 A2 f [x1 x2]. apply (@measure_induction _ (uncurry2 f)). clear x1 x2.
  intros [x1 x2] H. apply Acc_intro. intros [y1 y2] Lt. apply~ H.
Qed.

#[global]
Hint Resolve wf_measure2 : wf.


(* ---------------------------------------------------------------------- *)
(** Extension of LibTactic's [induction_wf] tactic for [measure] *)

Ltac induction_wf_process_wf_hyp tt ::= (* original in LibTactics *)
  match goal with
  | |- wf _ => auto with wf
  | |- well_founded _ => change well_founded with wf; auto with wf
  end.

Ltac induction_wf_process_measure E ::= (* original in LibTactics *)
  applys well_founded_ind (wf_measure E).


(* ********************************************************************** *)
(** * Construction of well-founded relations *)

(* ---------------------------------------------------------------------- *)
(** ** Empty relation *)

Lemma wf_empty : forall A,
  wf (@empty A).
Proof using. intros_all. constructor. introv H. false. Qed.

#[global]
Hint Resolve wf_empty : wf.


(* ---------------------------------------------------------------------- *)
(** ** Inclusion *)

(** Well-foundedness preserved by inclusion *)

Lemma wf_of_rel_incl : forall A (R1 R2 : binary A),
  wf R1 ->
  rel_incl R2 R1 ->
  wf R2.
Proof using.
  introv W1 Inc. intros x.
  pattern x. apply (well_founded_ind W1). clear x.
  intros x IH. constructor. intros. apply IH. apply~ Inc.
Qed.


(* ********************************************************************** *)
(* * Classic well-founded relations on [nat] *)

(* ---------------------------------------------------------------------- *)
(** ** [Peano.lt] on [nat] *)

(** The relation "less than" on natural numbers is well_founded. *)

Lemma wf_peano_lt : wf Peano.lt.
Proof using.
  intros x.
  induction x using peano_induction. apply~ Acc_intro.
    intros. applys H. math.
Qed.

#[global]
Hint Resolve wf_peano_lt : wf.


(* ---------------------------------------------------------------------- *)
(** ** [lt] on [nat] *)

(** The relation "less than" on natural numbers is well_founded. *)

Lemma wf_lt : @wf nat lt.
Proof using.
  intros x.
  induction x using peano_induction. apply~ Acc_intro.
Qed.

#[global]
Hint Resolve wf_lt : wf.


(* ---------------------------------------------------------------------- *)
(** ** The relation "greater than" on the set of
       natural number lower than a fixed upper bound. *)

Definition nat_upto (b:nat) :=
  fun (n m:nat) => (n <= b)%nat /\ (m < n)%nat.

Lemma nat_upto_eq : forall (b n m:nat),
  nat_upto b n m = ((n <= b)%nat /\ (m < n)%nat).
Proof using. auto. Qed.

Lemma wf_nat_upto : forall (b:nat),
  wf (nat_upto b).
Proof using.
  intros b n.
  induction_wf IH: (wf_measure (fun n => (b-n)%nat)) n.
  apply Acc_intro. introv [H1 H2]. apply IH.
  hnf. nat_math.
Qed.


(* ********************************************************************** *)
(* * Classic well-founded relations on [Z] *)

(* ---------------------------------------------------------------------- *)
(** ** The relation "less than" on the set of
       integers greater than a fixed lower bound. *)

Definition downto (b:Z) :=
  fun (n m:Z) => (b <= n) /\ (n < m).

Lemma downto_eq : forall (b n m:Z),
  downto b n m = (b <= n /\ n < m).
Proof using. auto. Qed.

Lemma downto_intro : forall (b n m:Z),
  b <= n ->
  n < m ->
  downto b n m.
Proof using. split~. Qed.

Lemma wf_downto : forall (b:Z),
  wf (downto b).
Proof using.
  intros b n.
  induction_wf IH: (wf_measure (fun n => Z.abs_nat (n-b))) n.
  apply Acc_intro. introv [H1 H2]. apply IH.
  unfolds. applys lt_abs_abs; math.
Qed.

#[global]
Hint Resolve wf_downto : wf.
#[global]
Hint Unfold downto.
#[global]
Hint Extern 1 (downto _ _ _) => math : maths.


(* ---------------------------------------------------------------------- *)
(** ** The relation "greater than" on the set of
       integers lower than a fixed upper bound. *)

Definition upto (b:Z) :=
  fun (n m:Z) => (n <= b) /\ (m < n).

Lemma upto_eq : forall b n m,
  upto b n m = ((n <= b) /\ (m < n)).
Proof using. auto. Qed.

Lemma upto_intro : forall b n m,
  n <= b ->
  m < n ->
  upto b n m.
Proof using. split~. Qed.

Lemma wf_upto : forall n,
  wf (upto n).
Proof using.
  intros b n.
  induction_wf IH: (wf_measure (fun n => Z.abs_nat (b-n))) n.
  apply Acc_intro. introv [H1 H2]. apply IH.
  applys lt_abs_abs; math.
Qed.

#[global]
Hint Resolve wf_upto : wf.
#[global]
Hint Unfold upto.
#[global]
Hint Extern 1 (upto _ _ _) => math : maths.


(* ********************************************************************** *)
(** * Inverse projections *)

Section UnprojWf.
Variables (A1 A2 A3 A4 A5 : Type).

Lemma wf_unproj21 : forall (R:binary A1),
  wf R ->
  wf (unproj21 A2 R).
Proof using.
  intros R H [x1 x2]. gen x2.
  induction_wf IH: H x1. constructor. intros [y1 y2]. auto.
Qed.

Lemma wf_unproj22 : forall (R:binary A2),
  wf R ->
  wf (unproj22 A1 R).
Proof using.
  intros R H [x1 x2]. gen x1.
  induction_wf IH: H x2. constructor. intros [y1 y2]. auto.
Qed.

Lemma wf_unproj31 : forall (R:binary A1),
  wf R ->
  wf (unproj31 A2 A3 R).
Proof using.
  intros R H [[x1 x2] x3]. gen x2 x3.
  induction_wf IH: H x1. constructor. intros [[y1 y2] y3]. auto.
Qed.

Lemma wf_unproj32 : forall (R:binary A2),
  wf R ->
  wf (unproj32 A1 A3 R).
Proof using.
  intros R H [[x1 x2] x3]. gen x1 x3.
  induction_wf IH: H x2. constructor. intros [[y1 y2] y3]. auto.
Qed.

Lemma wf_unproj33 : forall (R:binary A3),
  wf R ->
  wf (unproj33 A1 A2 R).
Proof using.
  intros R H [[x1 x2] x3]. gen x1 x2.
  induction_wf IH: H x3. constructor. intros [[y1 y2] y3]. auto.
Qed.

Lemma wf_unproj41 : forall (R:binary A1),
  wf R ->
  wf (unproj41 A2 A3 A4 R).
Proof using.
  intros R H [[[x1 x2] x3] x4]. gen x2 x3 x4.
  induction_wf IH: H x1. constructor. intros [[[y1 y2] y3] y4]. auto.
Qed.

Lemma wf_unproj42 : forall (R:binary A2),
  wf R ->
  wf (unproj42 A1 A3 A4 R).
Proof using.
  intros R H [[[x1 x2] x3] x4]. gen x1 x3 x4.
  induction_wf IH: H x2. constructor. intros [[[y1 y2] y3] y4]. auto.
Qed.

Lemma wf_unproj43 : forall (R:binary A3),
  wf R ->
  wf (unproj43 A1 A2 A4 R).
Proof using.
  intros R H [[[x1 x2] x3] x4]. gen x1 x2 x4.
  induction_wf IH: H x3. constructor. intros [[[y1 y2] y3] y4]. auto.
Qed.

Lemma wf_unproj44 : forall (R:binary A4),
  wf R ->
  wf (unproj44 A1 A2 A3 R).
Proof using.
  intros R H [[[x1 x2] x3] x4]. gen x1 x2 x3.
  induction_wf IH: H x4. constructor. intros [[[y1 y2] y3] y4]. auto.
Qed.

Lemma wf_unproj51 : forall (R:binary A1),
  wf R ->
  wf (unproj51 A2 A3 A4 A5 R).
Proof using.
  intros R H [[[[x1 x2] x3] x4] x5]. gen x2 x3 x4 x5.
  induction_wf IH: H x1. constructor. intros [[[[y1 y2] y3] y4] y5]. auto.
Qed.

End UnprojWf.

#[global]
Hint Resolve
  wf_unproj21 wf_unproj22
  wf_unproj31 wf_unproj32 wf_unproj33
  wf_unproj41 wf_unproj42 wf_unproj43 wf_unproj44
  wf_unproj51 : wf.


(* ********************************************************************** *)
(** * Lexicographical product *)

Lemma wf_lexico2 : forall A1 A2
 (R1:binary A1) (R2:binary A2),
  wf R1 ->
  wf R2 ->
  wf (lexico2 R1 R2).
Proof using.
  introv W1 W2. intros [x1 x2]. gen x2.
  induction_wf IH1: W1 x1. intros.
  induction_wf IH2: W2 x2. constructor. intros [y1 y2] H.
  simpls. destruct H as [H1|[H1 H2]].
  apply~ IH1. rewrite H1. apply~ IH2.
Qed.

Lemma wf_lexico3 : forall A1 A2 A3
 (R1:binary A1) (R2:binary A2) (R3:binary A3),
  wf R1 ->
  wf R2 ->
  wf R3 ->
  wf (lexico3 R1 R2 R3).
Proof using.
  intros. apply~ wf_lexico2. apply~ wf_lexico2.
Qed.

Lemma wf_lexico4 : forall A1 A2 A3 A4
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4),
  wf R1 ->
  wf R2 ->
  wf R3 ->
  wf R4 ->
  wf (lexico4 R1 R2 R3 R4).
Proof using.
  intros. apply~ wf_lexico3. apply~ wf_lexico2.
Qed.

#[global]
Hint Resolve wf_lexico2 wf_lexico3 wf_lexico4 : wf.


(* ********************************************************************** *)
(** * Symmetric product *)

Lemma wf_prod2_of_wf_1 : forall (A1 A2:Type)
 (R1:binary A1) (R2:binary A2),
  wf R1 ->
  wf (prod2 R1 R2).
Proof using.
  introv W1. intros [x1 x2].
  gen x2. induction_wf IH: W1 x1. intros.
  constructor. intros [y1 y2] [E1 E2]. apply~ IH.
Qed.

Lemma wf_prod2_of_wf_2 : forall (A1 A2:Type)
 (R1:binary A1) (R2:binary A2),
  wf R2 ->
  wf (prod2 R1 R2).
Proof using.
  introv W2. intros [x1 x2].
  gen x1. induction_wf IH: W2 x2. intros.
  constructor. intros [y1 y2] [E1 E2]. apply~ IH.
Qed.

Lemma wf_prod3_of_wf_1 : forall (A1 A2 A3:Type)
 (R1:binary A1) (R2:binary A2) (R3:binary A3),
  wf R1 ->
  wf (prod3 R1 R2 R3).
Proof using. intros. apply wf_prod2_of_wf_1. apply~ wf_prod2_of_wf_1. Qed.

Lemma wf_prod3_of_wf_2 : forall (A1 A2 A3:Type)
 (R1:binary A1) (R2:binary A2) (R3:binary A3),
  wf R2 ->
  wf (prod3 R1 R2 R3).
Proof using. intros. apply wf_prod2_of_wf_1. apply~ wf_prod2_of_wf_2. Qed.

Lemma wf_prod3_of_wf_3 : forall (A1 A2 A3:Type)
 (R1:binary A1) (R2:binary A2) (R3:binary A3),
  wf R3 ->
  wf (prod3 R1 R2 R3).
Proof using. intros. apply~ wf_prod2_of_wf_2. Qed.

Lemma wf_prod4_of_wf_1 : forall (A1 A2 A3 A4:Type)
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4),
  wf R1 ->
  wf (prod4 R1 R2 R3 R4).
Proof using. intros. apply wf_prod2_of_wf_1. apply~ wf_prod3_of_wf_1. Qed.

Lemma wf_prod4_of_wf_2 : forall (A1 A2 A3 A4:Type)
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4),
  wf R2 ->
  wf (prod4 R1 R2 R3 R4).
Proof using. intros. apply wf_prod2_of_wf_1. apply~ wf_prod3_of_wf_2. Qed.

Lemma wf_prod4_of_wf_3 : forall (A1 A2 A3 A4:Type)
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4),
  wf R3 ->
  wf (prod4 R1 R2 R3 R4).
Proof using. intros. apply wf_prod2_of_wf_1. apply~ wf_prod3_of_wf_3. Qed.

Lemma wf_prod4_of_wf_4 : forall (A1 A2 A3 A4:Type)
 (R1:binary A1) (R2:binary A2) (R3:binary A3) (R4:binary A4),
  wf R4 ->
  wf (prod4 R1 R2 R3 R4).
Proof using. intros. apply~ wf_prod2_of_wf_2. Qed.

#[global]
Hint Resolve
  wf_prod2_of_wf_1 wf_prod2_of_wf_2
  wf_prod3_of_wf_1 wf_prod3_of_wf_2 wf_prod3_of_wf_3
  wf_prod4_of_wf_1 wf_prod4_of_wf_2 wf_prod4_of_wf_3 wf_prod4_of_wf_4 : wf.


(* ********************************************************************** *)
(** * Well-foundedness of a function image *)

Lemma wf_rel_preimage : forall A B (R:binary B) (f:A->B),
  wf R ->
  wf (rel_preimage R f).
Proof using.
  introv W. intros x. gen_eq a: (f x). gen x.
  induction_wf IH: W a. introv E. constructors.
  intros y Hy. subst a. hnf in Hy. applys* IH.
Qed.

#[global]
Hint Resolve wf_rel_preimage : wf.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* TEMPORARY *)

(* begin hide *)

(* ********************************************************************** *)
(** * Union *)

(* --TODO..

Section WfUnion.
  Variables (A : Type).
  Variables R1 R2 : binary A.

  Notation Union := (union A R1 R2).

  Remark strip_commut :
    commut A R1 R2 ->
    forall x y:A,
      clos_trans A R1 y x ->
      forall z:A, R2 z y ->  exists2 y' : A, R2 y' x & clos_trans A R1 z y'.
  Proof using.
    induction 2 as [x y| x y z H0 IH1 H1 IH2]; intros.
    elim H with y x z; auto with sets; intros x0 H2 H3.
    exists x0; auto with sets.

    elim IH1 with z0; auto with sets; intros.
    elim IH2 with x0; auto with sets; intros.
    exists x1; auto with sets.
    apply t_trans with x0; auto with sets.
  Qed.


  Lemma Acc_union :
    commut A R1 R2 ->
    (forall x:A, Acc R2 x -> Acc R1 x) -> forall a:A, Acc R2 a -> Acc Union a.
  Proof using.
    induction 3 as [x H1 H2].
    apply Acc_intro; intros.
    elim H3; intros; auto with sets.
    cut (clos_trans A R1 y x); auto with sets.
    elimtype (Acc (clos_trans A R1) y); intros.
    apply Acc_intro; intros.
    elim H8; intros.
    apply H6; auto with sets.
    apply t_trans with x0; auto with sets.

    elim strip_commut with x x0 y0; auto with sets; intros.
    apply Acc_inv_trans with x1; auto with sets.
    unfold union in |- *.
    elim H11; auto with sets; intros.
    apply t_trans with y1; auto with sets.

    apply (Acc_clos_trans A).
    apply Acc_inv with x; auto with sets.
    apply H0.
    apply Acc_intro; auto with sets.
  Qed.


  Theorem wf_union :
    commut A R1 R2 -> well_founded R1 -> well_founded R2 -> well_founded Union.
  Proof using.
    unfold well_founded in |- *.
    intros.
    apply Acc_union; auto with sets.
  Qed.

End WfUnion.

*)

(* --TODO: Disjoint union, useful? *)

(* end hide *)

(* ********************************************************************** *)
(** * Transitive closure *)

Lemma wf_tclosure : forall A (R:binary A),
  wf R ->
  wf (tclosure R).
Proof using.
  unfold wf, well_founded.
  introv HAcc. intro a. specializes HAcc a. generalize dependent a.
  induction 1 as [ a _ IH ].
  constructor. intros b Hba.
  generalize a b Hba IH. clear a b Hba IH.
  induction 1; eauto using Acc_inv.
Qed.

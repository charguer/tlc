(* TEMPORARY FOR BACKWARD COMPATIBILITY 

(************************************************************)
(************************************************************)
(************************************************************)
(* LibNat *)


(* ********************************************************************** *)
(** * Simplification lemmas *)

(* ---------------------------------------------------------------------- *)
(** ** Addition and substraction *)


Hint Rewrite plus_zero_r plus_zero_l minus_zero : rew_nat.


(* ---------------------------------------------------------------------- *)
(** ** Comparison -- DEPRECATED? *)

Section CompProp.
Implicit Types a b c n m : nat.

Lemma le_SS : forall n m, (S n <= S m) = (n <= m).
Proof using. nat_math. Qed.
Lemma ge_SS : forall n m, (S n >= S m) = (n >= m).
Proof using. nat_math. Qed.
Lemma lt_SS : forall n m, (S n < S m) = (n < m).
Proof using. nat_math. Qed.
Lemma gt_SS : forall n m, (S n > S m) = (n > m).
Proof using. nat_math. Qed.

Lemma plus_le_l : forall a b c,
  (a + b <= a + c) = (b <= c).
Proof using. nat_math. Qed.
Lemma plus_ge_l : forall a b c,
  (a + b >= a + c) = (b >= c).
Proof using. nat_math. Qed.
Lemma plus_lt_l : forall a b c,
  (a + b < a + c) = (b < c).
Proof using. nat_math. Qed.
Lemma plus_gt_l : forall a b c,
  (a + b > a + c) = (b > c).
Proof using. nat_math. Qed.

Lemma plus_le_r : forall a b c,
  (b + a <= c + a) = (b <= c).
Proof using. nat_math. Qed.
Lemma plus_ge_r : forall a b c,
  (b + a >= c + a) = (b >= c).
Proof using. nat_math. Qed.
Lemma plus_lt_r : forall a b c,
  (b + a < c + a) = (b < c).
Proof using. nat_math. Qed.
Lemma plus_gt_r : forall a b c,
  (b + a > c + a) = (b > c).
Proof using. nat_math. Qed.

End CompProp.


(* ---------------------------------------------------------------------- *)
(** ** Simplification tactic *)

(** [rew_nat] performs some basic simplification on
    expressions involving natural numbers *)

Hint Rewrite le_SS ge_SS lt_SS gt_SS : rew_nat.
Hint Rewrite plus_le_l plus_ge_l plus_lt_l plus_gt_l : rew_nat.
Hint Rewrite plus_le_r plus_ge_r plus_lt_r plus_gt_r : rew_nat.

Tactic Notation "rew_nat" :=
  autorewrite with rew_nat.
Tactic Notation "rew_nat" "~" :=
  rew_nat; auto_tilde.
Tactic Notation "rew_nat" "*" :=
  rew_nat; auto_star.
Tactic Notation "rew_nat" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_nat).
  (* autorewrite with rew_nat in *. *)
Tactic Notation "rew_nat" "~" "in" "*" :=
  rew_nat in *; auto_tilde.
Tactic Notation "rew_nat" "*" "in" "*" :=
  rew_nat in *; auto_star.
Tactic Notation "rew_nat" "in" hyp(H) :=
  autorewrite with rew_nat in H.
Tactic Notation "rew_nat" "~" "in" hyp(H) :=
  rew_nat in H; auto_tilde.
Tactic Notation "rew_nat" "*" "in" hyp(H) :=
  rew_nat in H; auto_star.




(* ********************************************************************** *)
(** * -- TODO: Other operations and lemmas (not stable) *)

(* ---------------------------------------------------------------------- *)
(** ** Div *)

Definition div (n q : nat) :=
  match q with
  | 0 => 0
  | S predq =>
  let aux := fix aux (m r : nat) {struct m} :=
    match m,r with
    | 0, _ => 0
    | S m',0 => (1 + aux m' predq)%nat
    | S m', S r' => aux m' r'
    end in
  aux n predq
  end.


(* ---------------------------------------------------------------------- *)
(** ** Div2 *)



(* ---------------------------------------------------------------------- *)
(** ** Factorial *)

Fixpoint factorial (n:nat) : nat :=
  match n with
  | 0 => 1
  | S n' => n * (factorial n')
  end.





(************************************************************)
(************************************************************)
(************************************************************)
(* LibInt *)

(* ---------------------------------------------------------------------- *)
(** ** Calling [maths] after eliminating boolean reflection *)

(** [maths] is a more powerful version of [math],
    able to deconstruct conjunctions, disjunctions,
    and negations, but as a consequence it might be slower. *)

Hint Rewrite istrue_and istrue_or istrue_neg : rew_reflect_and_or_neg.

Ltac maths_core tt :=
  autorewrite with rew_reflect_and_or_neg in *; intuition math.

Tactic Notation "maths" :=
  maths_core tt.



(* ---------------------------------------------------------------------- *)
(** ** Extend [zify] to handle [Z.to_nat]. *)

Lemma Z_of_nat_zify : forall x, Z.of_nat (Z.to_nat x) = Z.max 0 x.
Proof using.
  intros x. destruct x.
  - rewrite Z2Nat.id; reflexivity.
  - rewrite Z2Nat.inj_pos. math_lia.
  - rewrite Z2Nat.inj_neg. math_lia.
Qed.

Ltac zify_nat_op_extended :=
  match goal with
  | H : context [ Z.of_nat (Z.to_nat ?a) ] |- _ => rewrite (Z_of_nat_zify a) in H
  | |- context [ Z.of_nat (Z.to_nat ?a) ] => rewrite (Z_of_nat_zify a)
  | _ => zify_nat_op
  end.

Ltac zify_nat ::= repeat zify_nat_rel; repeat zify_nat_op_extended; unfold Z_of_nat' in *.



(************************************************************)
(* * Pow function *)

Require Import Zpow_facts.

Lemma power_pos:
  forall k n,
  0 < n ->
  0 <= k ->
  1 <= n^k.
Proof using.
  intros. math_rewrite (1 = n^0). reflexivity.
  apply Zpower_le_monotone; math.
Qed.

Lemma pow2_pos : forall n, n >= 0 -> 2^n >= 1.
Proof using.
  intros. forwards: power_pos n 2; math.
Qed.

Lemma pow2_succ : forall n, n >= 0 -> 2^(n+1) = 2*2^n.
Proof using.
  intros. math_rewrite (n+1 = Zsucc n).
  rewrite Zpower_Zsucc; math.
Qed.

(* A tactic that helps dealing with goals containing "b^m" for multiple m *)
Require Import List.

Ltac subst_eq_boxer_list l rewrite_tac :=
  match l with
  | nil => idtac
  | (@boxer _ ?p) :: ?Hs =>
    match p with
      (?tm, ?Htm) =>
      rewrite_tac Htm; clear Htm; clear tm;
      subst_eq_boxer_list Hs rewrite_tac
    end
  end.

(* Develop occurences of (b ^ m) in H into (b ^ (m - min_e) * b ^ min_e).
   (and try to simplify/compute b^(m - min_e)).
 *)
Ltac rew_pow_develop b m min_e H :=
  let m_eq_plusminus := fresh in
  assert (m = min_e + (m - min_e)) as m_eq_plusminus
      by (rewrite Zplus_minus; reflexivity);
  rewrite m_eq_plusminus in H; clear m_eq_plusminus;
  rewrite (Z.pow_add_r b min_e (m - min_e)) in H; [
    rewrite Z.mul_comm in H;
    let tm' := fresh "tm'" in
    let H' := fresh "H'" in
    remember (b ^ (m - min_e)) as tm' eqn:H' in H;
    let e := fresh "e" in
    evar (e: int);
    let Heqe := fresh in
    assert (e = m - min_e) as Heqe
        by (ring_simplify; subst e; reflexivity);
    rewrite <-Heqe in H'; clear Heqe; unfold e in H'; ring_simplify in H';
    rewrite H' in H; clear H'; clear tm'; clear e;
    try rewrite Z.mul_1_l in H
  | ring_simplify; auto with zarith ..].

Ltac rew_pow_aux_goal b min_e normalized_acc :=
  match goal with
  | |- context [ b ^ ?m ] =>
    let tm := fresh "tm" in
    let Heqtm := fresh "Heqtm" in
    remember (b ^ m) as tm eqn:Heqtm in |- *;
    rew_pow_develop b m min_e Heqtm; [
      rew_pow_aux_goal b min_e ((boxer (tm, Heqtm)) :: normalized_acc)
    | ..]
  | _ => subst_eq_boxer_list normalized_acc ltac:(fun E => rewrite E)
  end.

Ltac rew_pow_aux_in b min_e H normalized_acc :=
  match type of H with
  | context [ b ^ ?m ] =>
    let tm := fresh "tm" in
    let Heqtm := fresh "Heqtm" in
    remember (b ^ m) as tm eqn:Heqtm in H;
    rew_pow_develop b m min_e Heqtm; [
      rew_pow_aux_in b min_e H ((boxer (tm, Heqtm)) :: normalized_acc)
    | ..]
  | _ => subst_eq_boxer_list normalized_acc ltac:(fun E => rewrite E in H)
  end.

Tactic Notation "rew_pow" constr(b) constr(min_e) :=
  rew_pow_aux_goal b min_e (@nil Boxer).
Tactic Notation "rew_pow" "~" constr(b) constr(min_e) :=
  rew_pow_aux_goal b min_e (@nil Boxer); auto_tilde.
Tactic Notation "rew_pow" "*" constr(b) constr(min_e) :=
  rew_pow_aux_goal b min_e (@nil Boxer); auto_star.
Tactic Notation "rew_pow" constr(b) constr(min_e) "in" hyp(H) :=
  rew_pow_aux_in b min_e H (@nil Boxer).
Tactic Notation "rew_pow" "~" constr(b) constr(min_e) "in" hyp(H) :=
  rew_pow_aux_in b min_e H (@nil Boxer); auto_tilde.
Tactic Notation "rew_pow" "*" constr(b) constr(min_e) "in" hyp(H) :=
  rew_pow_aux_in b min_e H (@nil Boxer); auto_star.

(* Test  -- TODO: move *)
(* Axiom P : int -> Prop.  *)
(* Goal forall n, P (1 + 2 ^ (n + 3) + 2 ^ n + 2 ^ (n+1)). *)
(* Proof. *)
(*   intros. *)
(*   skip_asserts: (3 = 2 ^ (n+3)). rew_pow 2 n in H. *)
(*   rew_pow 2 n. *)
(* Admitted. *)



(************************************************************)
(* * Min function *)

Require Import LibEpsilon.

Instance int_le_total_order : Le_total_order (A:=int).
Proof using.
  constructor. constructor. constructor; unfolds.
  math. math. unfolds. math. unfolds.
  intros. tests: (x <= y). left~. right. math.
Qed.

(* todo: make polymorphic with classes *)

Section Min.
Implicit Types x y : int.

Definition min x y :=
  If x <= y then x else y.

Lemma min_self : forall x,
  min x x = x.
Proof using. intros. unfolds min. case_if~. Qed.

Lemma min_left : forall x y,
  x <= y -> 
  min x y = x.
Proof using. intros. unfolds min. case_if~. false*. Qed.

Lemma min_right : forall x y,
  y <= x ->
  min x y = y.
Proof using. intros. unfolds min. case_if~. apply~ le_antisym. Qed.

Lemma min_trans_inv : forall a b x y : int,
  min a b <= x -> 
  y < a -> 
  y < b -> 
  y < x.
Proof using. intros. unfolds min. case_if; math. Qed.

End Min.



(************************************************************)
(* ---------------------------------------------------------------------- *)
(** ** Comparison *)

Lemma plus_le_l : forall a b c,
  (a + b <= a + c) = (b <= c).
Proof using. math. Qed.
Lemma plus_ge_l : forall a b c,
  (a + b >= a + c) = (b >= c).
Proof using. math. Qed.
Lemma plus_lt_l : forall a b c,
  (a + b < a + c) = (b < c).
Proof using. math. Qed.
Lemma plus_gt_l : forall a b c,
  (a + b > a + c) = (b > c).
Proof using. math. Qed.

Lemma plus_le_r : forall a b c,
  (b + a <= c + a) = (b <= c).
Proof using. math. Qed.
Lemma plus_ge_r : forall a b c,
  (b + a >= c + a) = (b >= c).
Proof using. math. Qed.
Lemma plus_lt_r : forall a b c,
  (b + a < c + a) = (b < c).
Proof using. math. Qed.
Lemma plus_gt_r : forall a b c,
  (b + a > c + a) = (b > c).
Proof using. math. Qed.

Hint Rewrite plus_le_l plus_ge_l plus_lt_l plus_gt_l : rew_int.
Hint Rewrite plus_le_r plus_ge_r plus_lt_r plus_gt_r : rew_int.



(* ********************************************************************** *)
(** * Advanced induction *)

(* --TODO: move to LibNat *)
(* --TODO: document and explain when this is needed *)

Definition eq_gt_implies (P : (nat->Prop) -> Prop) :=
  forall n, 
  (forall m, n > m -> P (eq m)) -> 
  P (gt n).

Definition eq_lt_implies (P : (nat->Prop) -> Prop) :=
  forall n, 
  (forall m, n < m -> P (eq m)) -> 
  P (gt n).

Hint Unfold eq_lt_implies eq_gt_implies. (* --TODO: rename *)

Lemma eq_lt_induction : forall (P : (nat->Prop) -> Prop),
  (forall n, (forall m, n > m -> P (eq m)) -> P (lt n)) ->
  (forall n, P (lt n) -> P (eq n)) ->
  (forall n, P (eq n)).
Proof using. intros. induction n using peano_induction. auto. Qed.

Lemma eq_gt_induction : forall (P : (nat->Prop) -> Prop),
  (forall n, (forall m, n > m -> P (eq m)) -> P (gt n)) ->
  (forall n, P (gt n) -> P (eq n)) ->
  (forall n, P (eq n)).
Proof using. intros. induction n using peano_induction. auto. Qed.

Lemma eq_gt_induction_2 : forall (P1 P2 : (nat->Prop) -> Prop),
  eq_gt_implies P1 -> 
  eq_gt_implies P2 ->
  (forall n, P1 (gt n) -> P2 (gt n) -> P1 (eq n) /\ P2 (eq n)) ->
     (forall n, P1 (eq n)) 
  /\ (forall n, P2 (eq n)).
Proof using.
  introv H1 H2 R.
  cuts M: (forall n, P1 (eq n) /\ P2 (eq n)).
    split; intros n; specializes M n; autos*.
  induction n using peano_induction. apply R;
    match goal with K: eq_gt_implies ?Pi |- ?Pi _ =>
      apply K; intros; forwards*: H; try math end.
Qed.

(* --TODO add missing arities *)

Lemma eq_gt_induction_5 : forall (P1 P2 P3 P4 P5 : (nat->Prop) -> Prop),
  eq_gt_implies P1 -> 
  eq_gt_implies P2 -> 
  eq_gt_implies P3 ->
  eq_gt_implies P4 -> 
  eq_gt_implies P5 ->
  (forall n, P1 (gt n) -> P2 (gt n) -> P3 (gt n) -> P4 (gt n) -> P5 (gt n) ->
    P1 (eq n) /\ P2 (eq n) /\ P3 (eq n) /\ P4 (eq n) /\ P5 (eq n)) ->
     (forall n, P1 (eq n))
  /\ (forall n, P2 (eq n)) 
  /\ (forall n, P3 (eq n))
  /\ (forall n, P4 (eq n))  
  /\ (forall n, P5 (eq n)).
Proof using.
  introv H1 H2 H3 H4 H5 R.
  cuts M: (forall n, P1 (eq n) /\ P2 (eq n) /\ P3 (eq n) /\ P4 (eq n) /\ P5 (eq n)).
    splits; intros n; specializes M n; autos*.
  induction n using peano_induction. apply R;
    match goal with K: eq_gt_implies ?Pi |- ?Pi _ =>
      apply K; intros; forwards*: H; try math end.
Qed.



(* ---------------------------------------------------------------------- *)
(** ** Modulo function *)

Lemma mod_eq_prove : forall k a b n,
  a = b + k * n -> a mod n = b mod n.
Proof using. intros. subst. rewrite~ Z_mod_plus_full. Qed.

Lemma mod_prove : forall k a b n,
  a = b + k * n -> 0 <= b -> b < n -> a mod n = b.
Proof using.
  intros. rewrite <- (@Zmod_small b n).
  apply* mod_eq_prove. math.
Qed.

Lemma mod2_zero :
  0 mod 2 = 0.
Proof using. reflexivity. Qed.

Lemma mod2_odd : forall k,
  (2 * k) mod 2 = 0.
Proof using. intros. apply (mod_prove k); math. Qed.

Lemma mod2_even : forall k,
  (2 * k + 1) mod 2 = 1.
Proof using. intros. apply (mod_prove k); math. Qed.

Lemma div2_odd : forall k,
  (2 * k) / 2 = k.
Proof using.
  intros. math_rewrite (2*k=k*2).
  apply Z_div_mult_full. math.
Qed.

Lemma div2_even : forall k,
  k >= 0 -> (2 * k + 1) / 2 = k.
Proof using. intros. symmetry. eapply Zdiv_unique with (r:=1); math. Qed.

Lemma mod2_bound : forall n,
  0 <= n mod 2 < 2.
Proof using. (* using stdlib *)
  intros. forwards: (Z_mod_remainder n 2). math.
  destruct H as [[? ?]|[? ?]]; math.
Qed.

Lemma div2_bounds : forall m n,
  m = n / 2 -> 2 * m <= n /\ n <= 2 * m + 1.
Proof using. (* using stdlib *)
  intros. lets K: (Z_div_mod_eq n 2) __. math. (* TODO: forwards shouldn't do simpl *)
  rewrite <- H in K.
  lets [E1 E2]: (mod2_bound n). math.
Qed.

Implicit Arguments div2_bounds [m n].


Hint Rewrite mod2_zero mod2_odd mod2_even div2_odd div2_even : rew_parity.

Ltac rew_parity :=
  autorewrite with rew_parity.



(* ---------------------------------------------------------------------- *)
(** ** Comparison lifted *)

Lemma nat_int_lt : forall (n m:nat),
  n < m -> 
  (n:int) < (m:int).
Proof using. math. Qed.

Lemma nat_int_le : forall (x y:nat),
  x <= y -> 
  ((x:int) <= (y:int)).
Proof using. math. Qed.

Lemma nat_int_ge : forall (x y:nat),
  x >= y -> 
  (x:int) >= (y:int).
Proof using. math. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Lia/Nia *)


Ltac nat_math_lia :=
  nat_math_setup; lia.

Ltac nat_math_nia :=
  nat_math_setup; nia.

Require Import Psatz.



(* ---------------------------------------------------------------------- *)
(** ** [math_lia], [math_nia], [math_dia] tactic *)

(** --DISCLAIMER: WORK IN PROGRESS *) 

(* Require the CSDP package to be installed *)

(** [math_lia] supports linear arithmetic; it roughly provides the
    combined power of [ring_simplify] and [omega]. *)

Tactic Notation "math_lia" := math_debug; lia.

(** [math_nia] supports non-linear integer arithmetic.
    It performs a limited amount of non-linear reasoning
    before running [lia]. *)

Tactic Notation "math_nia" := math_debug; nia.

(** [math_dia] extends [math_nia] with support for divisions.
    Division are encoded using multiplications, via Euclidian
    division and remainder. *)

Definition Zdiv_hyp (P:Prop) := P.

Lemma Z_div_mod' : forall a b : int,
  Zdiv_hyp ((b > 0)%Z) ->
  let (q, r) := Z.div_eucl a b in
  a = (b * q)%I + r /\ (0 <= r < b)%Z.
Proof using. applys Z_div_mod. Qed.

Ltac Zdiv_eliminate_step tt :=
  match goal with |- context[ Z.div_eucl ?X ?Y ] =>
     generalize (@Z_div_mod' X Y);
     destruct (Z.div_eucl X Y)
  end.

Ltac math_dia_generalize_all_prop tt :=
  repeat match goal with H: ?T |- _ =>
    match type of T with Prop => gen H end end.

Ltac Zdiv_eliminate tt :=
  math_dia_generalize_all_prop tt;
  unfold Z.div;
  repeat (Zdiv_eliminate_step tt).

(* todo: deal differently with iterated divisions,
   in order to avoid blow up *)

Ltac Zdiv_instantiate_hyp_steps tt :=
  match goal with H: Zdiv_hyp ?P -> _ |- _ =>
    specializes H __;
    [ idtac
    | try Zdiv_instantiate_hyp_steps tt ]
  end.

Ltac Zdiv_instantiate_hyp tt :=
  Zdiv_instantiate_hyp_steps tt.

Ltac math_dia_setup :=
  math_0; math_1; math_2; math_3; Zdiv_eliminate tt;
  intros; try Zdiv_instantiate_hyp_steps tt; unfolds Zdiv_hyp.

Tactic Notation "math_dia" :=
  math_dia_setup; math_nia.

(*--WORK IN PROGRESS

  Lemma math_nia_demo_1 : forall (a b N : int),
    N > 0 ->
    a * N <= b * N ->
    a <= b.
  Proof using. math_nia. Qed.

  Lemma math_dia_demo_1 : forall (a b t : int),
    t > 0 ->
    a <= b ->
    a / t <= b / t.
  Proof using. math_dia. Qed.

  Lemma math_dia_demo_2 : forall (a t : int),
    t > 1 ->
    a > 0 ->
    a / t <= a.
  Proof using. math_dia. Qed.

  Lemma math_dia_demo_3 : forall (a b t : int),
    t > 0 ->
    0 <= a <= b ->
    a / t <= b / t.
  Proof using. math_dia. Qed.

  Lemma math_dia_demo_4 : forall (a b N : int),
    N > 0 ->
    a > 0 ->
    b > 0 ->
    a * N <= b * N ->
    a <= b.
  Proof using. math_dia. Qed.

  Lemma math_dia_demo_5 : forall (a b N t : int),
    N > 0 ->
    t > 1 ->
    a > 0 ->
    b > 0 ->
    a * N <= b * N ->
    a / t <= b.
  Proof using.
    intros.
    (* math_dia_setup. math_dia. *)
    try math_dia.
    assert (a / t <= a). math_dia.
    assert (a <= b). math_dia.
    math_dia.
  Qed.

  Lemma math_dia_demo_span_1 : forall (a b t n N : int),
    N > 0 ->
    n > 0 ->
    t > 0 ->
    a >= 0 ->
    b >= 0 ->
    a <= b * (1 + N/t) + n * t/N ->
    (   a <= b * (1 + N/t) + (n+1) * t/N
    /\ (a+1) <= (b+1) * (1 + N/t) + (n+1) * t/N
    /\ b * (1 + N/t) + N * t/N = b * (1 + t/N) + t
    /\ (b + t) * (1 + N/t) + n * t/N = b * (1 + N/t) + t + N + n * t/N).
  Proof using.
    intros. splits.
    math_dia.
    try math_dia. skip.
    try math_dia. skip.
    try math_dia. skip.
  Qed.

  Lemma math_dia_demo : forall a b t n N,
    a * N <= b * N + (b + n) * t  ->
    a <= b * (1 + t / N) + n * t / N.
  Proof using. intros. math_dia. Qed.
---*)



Ltac math_lia := math_setup; lia.
Ltac math_nia := math_setup; nia.

(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* * LibOrder *)

(* ********************************************************************** *)
(* * Order modulo *)

(* TODO: deprecate this *)




(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* * LibWf *)


Lemma measure_2_induction : forall A B (mu : A -> B -> nat) (P : A -> B -> Prop),
  (forall x1 x2, (forall y1 y2, mu y1 y2 < mu x1 x2 -> P y1 y2) -> P x1 x2) ->
  (forall x1 x2, P x1 x2).
Proof using.
  introv H. intros x1 x2. gen_eq p: (x1,x2). gen x1 x2.
  induction_wf IH: (wf_measure (fun p => mu (fst p) (snd p))) p.
  introv E. destruct p. inverts E. apply H.
  introv L. apply* IH. simpl. auto.
Qed.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* * LibWf *)

(** [unfold_wf] and [unfolds_wf] are shorthands for unfolding
    combinators used in definitions related to well-foundedness. *)

Ltac unfold_wf_base :=
  unfold_unproj; unfold_uncurryp; 
  unfold lexico4, lexico3, lexico2.

Ltac unfolds_wf_base :=
  unfolds_unproj; unfolds_uncurryp; unfolds_lexico.

Tactic Notation "unfold_wf" :=
  unfold_wf_base.
Tactic Notation "unfold_wf" "~" :=
  unfold_wf; auto_tilde.
Tactic Notation "unfold_wf" "*" :=
  unfold_wf; auto_star.

Tactic Notation "unfolds_wf" :=
  unfolds_wf_base.
Tactic Notation "unfolds_wf" "~" :=
  unfolds_wf; auto_tilde.
Tactic Notation "unfolds_wf" "*" :=
  unfolds_wf; auto_star.


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* * LibFix *)


(* ********************************************************************** *)
(** * Extraction product *)

(* ---------------------------------------------------------------------- *)
(** ** Extraction for Caml *)

Extraction Language Ocaml.

Extract Constant FixFunMod =>
  "(fun bigf -> let rec f x = bigf f x in f)".

Extract Constant FixValMod =>
  "(fun bigf -> let rec x = lazy (Lazy.force (bigf x)) in x)".

Extract Constant FixValModMut2 =>
 "(fun f1 f2 ->
  let rec x1 = lazy (Lazy.force (f1 x1 x2))
      and x2 = lazy (Lazy.force (f2 x1 x2)) in
  Pair (x1,x2))".

(* optional
Extraction Inline FixFunMod.
Extraction Inline FixValMod.
Extraction Inline FixValModMut2.
*)

(* ---------------------------------------------------------------------- *)
(** ** Extraction for Haskell *)

Extraction Language Haskell.

Extract Constant Fix =>
  "(fun bigf => let x = bigf x in x)".



(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* * LibMultiset *)

Hint Resolve foreach_empty foreach_single foreach_union.

Hint Rewrite foreach_union_eq : rew_foreach.

Tactic Notation "rew_foreach" := 
  autorewrite with rew_foreach.
Tactic Notation "rew_foreach" "~" constr(H) :=
  rew_foreach H; auto_tilde.
Tactic Notation "rew_foreach" "*" constr(H) :=
  rew_foreach H; auto_star.
Tactic Notation "rew_foreach" hyp(H) := 
  autorewrite with rew_foreach in H.

(* -- TODO: share [rew_foreach] tactics in LibContainer *)




(* ********************************************************************** *)
(* ********************************************************************** *)
(* ********************************************************************** *)
(* * LibSet *)



(* ********************************************************************** *)
(** * Tactics *)

(* DEPRECATED, use "set_prove" when possible *)

(* ---------------------------------------------------------------------- *)
(** ** Tactics to prove equalities on unions *)

(* Documentation appears further on *)

Lemma for_set_union_assoc : forall A, 
  assoc (union (T:=set A)).
Proof using. intros. apply union_assoc. Qed.

Lemma for_set_union_comm : forall A,  
  comm (union (T:=set A)).
Proof using. intros. apply union_comm. Qed.

Lemma for_set_union_empty_l : forall A (E:set A), 
  \{} \u E = E.
Proof using. intros. apply union_empty_l. Qed.

Lemma for_set_union_empty_r : forall A (E:set A), 
  E \u \{} = E.
Proof using. intros. apply union_empty_r. Qed.

Hint Rewrite <- for_set_union_assoc : rew_permut_simpl.
Hint Rewrite for_set_union_empty_l for_set_union_empty_r : rew_permut_simpl.
Ltac rew_per :=
  autorewrite with rew_permut_simpl; try typeclass.
Ltac rews_permut_simpl :=
  autorewrite with rew_permut_simpl in *; try typeclass.

Section PermutationTactic.
Context (A:Type).
Implicit Types l : set A.

Lemma permut_get_1 : forall l1 l2,
  (l1 \u l2) = (l1 \u l2).
Proof using. intros. auto. Qed.

Lemma permut_get_2 : forall l1 l2 l3,
  (l1 \u l2 \u l3) = (l2 \u l1 \u l3).
Proof using. intros. apply union_comm_assoc. Qed.

Lemma permut_get_3 : forall l1 l2 l3 l4,
  (l1 \u l2 \u l3 \u l4) = (l2 \u l3 \u l1 \u l4).
Proof using.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_2.
Qed.

Lemma permut_get_4 : forall l1 l2 l3 l4 l5,
    (l1 \u l2 \u l3 \u l4 \u l5)
  = (l2 \u l3 \u l4 \u l1 \u l5).
Proof using.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_3.
Qed.

Lemma permut_get_5 : forall l1 l2 l3 l4 l5 l6,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l6)
  = (l2 \u l3 \u l4 \u l5 \u l1 \u l6).
Proof using.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_4.
Qed.

Lemma permut_get_6 : forall l1 l2 l3 l4 l5 l6 l7,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l6 \u l7)
  = (l2 \u l3 \u l4 \u l5 \u l6 \u l1 \u l7).
Proof using.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_5.
Qed.

Lemma permut_get_7 : forall l1 l2 l3 l4 l5 l6 l7 l8,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l6 \u l7 \u l8)
  = (l2 \u l3 \u l4 \u l5 \u l6 \u l7 \u l1 \u l8).
Proof using.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_6.
Qed.

Lemma permut_get_8 : forall l1 l2 l3 l4 l5 l6 l7 l8 l9,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l6 \u l7 \u l8 \u l9)
  = (l2 \u l3 \u l4 \u l5 \u l6 \u l7 \u l8 \u l1 \u l9).
Proof using.
  intros. do 2 rewrite (union_assoc l2). apply permut_get_7.
Qed.

Lemma permut_cancel_1 : forall l1 l2,
  (l1 \u l1 \u l2) = l1 \u l2.
Proof using. intros. rewrite union_assoc. rewrite union_self. auto. Qed.

Lemma permut_cancel_2 : forall l1 l2 l3,
  (l1 \u l2 \u l1 \u l3) = (l1 \u l2 \u l3).
Proof using.
  intros. rewrite <- (@permut_get_2 l1). apply permut_cancel_1.
Qed.

Lemma permut_cancel_3 : forall l1 l2 l3 l4,
  (l1 \u l2 \u l3 \u l1 \u l4) = (l1 \u l2 \u l3 \u l4).
Proof using.
  intros. rewrite <- (@permut_get_3 l1). apply permut_cancel_1.
Qed.

Lemma permut_cancel_4 : forall l1 l2 l3 l4 l5,
    (l1 \u l2 \u l3 \u l4 \u l1 \u l5)
  = (l1 \u l2 \u l3 \u l4 \u l5).
Proof using.
  intros. rewrite <- (@permut_get_4 l1). apply permut_cancel_1.
Qed.

Lemma permut_cancel_5 : forall l1 l2 l3 l4 l5 l6,
    (l1 \u l2 \u l3 \u l4 \u l5 \u l1 \u l6)
  = (l1 \u l2 \u l3 \u l4 \u l5 \u l6).
Proof using.
  intros. rewrite <- (@permut_get_5 l1). apply permut_cancel_1.
Qed.

Lemma permut_tactic_setup : forall l1 l2,
   (\{} \u l1 \u \{}) = (l2 \u \{}) -> l1 = l2.
Proof using. intros. rews_permut_simpl. Qed.

Lemma permut_tactic_keep : forall l1 l2 l3 l4,
  ((l1 \u l2) \u l3) = l4 ->
  (l1 \u (l2 \u l3)) = l4.
Proof using. intros. rews_permut_simpl. Qed.

Lemma permut_tactic_simpl : forall l1 l2 l3 l4,
  (l1 \u l3) = l4 ->
  (l1 \u (l2 \u l3)) = (l2 \u l4).
Proof using. intros. subst. apply permut_get_2. Qed.

Lemma permut_tactic_trans : forall l1 l2 l3,
  l3 = l2 -> l1 = l3 -> l1 = l2.
Proof using. intros. subst~. Qed.

End PermutationTactic.

(** [permut_lemma_get n] returns the lemma [permut_get_n]
    for the given value of [n] *)

Ltac permut_lemma_get n :=
  match number_to_nat n with
  | 1%nat => constr:(permut_get_1)
  | 2%nat => constr:(permut_get_2)
  | 3%nat => constr:(permut_get_3)
  | 4%nat => constr:(permut_get_4)
  | 5%nat => constr:(permut_get_5)
  end.

(** [permut_prepare] applies to a goal of the form [permut l l']
    and sets [l] and [l'] in the form [l1 \u l2 \u .. \u \{}],
    (some of the lists [li] are put in the form [x::\{}]). *)

Ltac permut_simpl_prepare :=
   rew_permut_simpl;
   apply permut_tactic_setup;
   repeat rewrite <- union_assoc.

(* todo : doc *)

Ltac cancel_all_dup l :=
  repeat first
    [ rewrite (permut_cancel_1 l)
    | rewrite (permut_cancel_2 l)
    | rewrite (permut_cancel_3 l)
    | rewrite (permut_cancel_4 l)
    | rewrite (permut_cancel_5 l) ].

Ltac permut_index_of l lcontainer :=
  match constr:(lcontainer) with
  | l \u _ => constr:(1)
  | _ \u l \u _ => constr:(2)
  | _ \u _ \u l \u _ => constr:(3)
  | _ \u _ \u _ \u l \u _ => constr:(4)
  | _ \u _ \u _ \u _ \u l \u _ => constr:(5)
  | _ \u _ \u _ \u _ \u _ \u l \u _ => constr:(6)
  | _ \u _ \u _ \u _ \u _ \u _ \u l \u _ => constr:(7)
  | _ \u _ \u _ \u _ \u _ \u _ \u _ \u l \u _ => constr:(8)
  | _ => constr:(0) (* not found *)
  end.

(** [permut_simplify] simplifies a goal of the form
    [permut l l'] where [l] and [l'] are lists built with
    concatenation and consing, by cancelling syntactically
    equal elements *)

Ltac permut_simpl_once :=
  match goal with
  | |- (_ \u \{}) = _ => fail 1
  | |- (_ \u (?l \u ?lr)) = ?l' =>
     cancel_all_dup l;
     match permut_index_of l l' with
     | 0 => apply permut_tactic_keep
     | ?n => let F := permut_lemma_get n in
            eapply permut_tactic_trans;
            [ eapply F; try typeclass
            | apply permut_tactic_simpl ]
     end
  end.

Ltac permut_simpl :=
  permut_simpl_prepare;
  repeat permut_simpl_once;
  rew_permut_simpl;
  try apply refl_equal.

(* TODO: move demos somewhere else *)

Section DemoSetUnion.
Variables (A:Type).

Lemma demo_set_union_permut_simpl_1 :
  forall l1 l2 l3 : set A,
  (l1 \u l2 \u l3 \u l1) = (l3 \u l2 \u l1).
Proof using.
  intros.
  permut_simpl_prepare.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  rew_permut_simpl.
Qed.


Lemma demo_set_union_permut_simpl_2 :
  forall
  (x:A) l1 l2 l3,
  (l1 \u \{x} \u l3 \u l2) = (l1 \u l2 \u (\{x} \u l3)).
Proof using.
  intros.
  permut_simpl_prepare.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  rew_permut_simpl.
Qed.

Lemma demo_set_union_permut_simpl_3 : forall (x y:A) l1 l1' l2 l3,
  l1 = l1' ->
    (l1 \u (\{x} \u l2) \u \{x} \u (\{y} \u l3)) 
  = (\{y} \u (l1' \u l2) \u (\{x} \u l3)).
Proof using.
  intros.
  permut_simpl_prepare.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  permut_simpl_once.
  try permut_simpl_once.
  rew_permut_simpl.
Qed.

End DemoSetUnion.

(* ---------------------------------------------------------------------- *)
(** ** Tactics to prove membership *)

(* DEPRECATED: use "set_prove" when possible *)

Section InUnionGet.
Variables (A:Type).
Implicit Types l : set A.

Lemma in_union_get_1 : forall x l1 l2,
  x \in l1 -> x \in (l1 \u l2).
Proof using. intros. apply in_union_l. auto. Qed.

Lemma in_union_get_2 : forall x l1 l2 l3,
  x \in l2 -> x \in (l1 \u l2 \u l3).
Proof using. intros. apply in_union_r. apply~ in_union_get_1. Qed.

Lemma in_union_get_3 : forall x l1 l2 l3 l4,
  x \in l3 -> x \in (l1 \u l2 \u l3 \u l4).
Proof using. intros. apply in_union_r. apply~ in_union_get_2. Qed.

Lemma in_union_get_4 : forall x l1 l2 l3 l4 l5,
  x \in l4 -> x \in (l1 \u l2 \u l3 \u l4 \u l5).
Proof using. intros. apply in_union_r. apply~ in_union_get_3. Qed.

Lemma in_union_get_5 : forall x l1 l2 l3 l4 l5 l6,
  x \in l5 -> x \in (l1 \u l2 \u l3 \u l4 \u l5 \u l6).
Proof using. intros. apply in_union_r. apply~ in_union_get_4. Qed.

End InUnionGet.

Arguments in_union_get_1 [A] [x] [l1] [l2].
Arguments in_union_get_2 [A] [x] [l1] [l2] [l3].
Arguments in_union_get_3 [A] [x] [l1] [l2] [l3] [l4].
Arguments in_union_get_4 [A] [x] [l1] [l2] [l3] [l4] [l5].
Arguments in_union_get_5 [A] [x] [l1] [l2] [l3] [l4] [l5] [l6].

Ltac in_union_get :=
  match goal with H: ?x \in ?A |- ?x \in ?B =>
  match B with context [A] =>
  let go tt := first
        [ apply (in_union_get_1 H)
        | apply (in_union_get_2 H)
        | apply (in_union_get_3 H)
        | apply (in_union_get_4 H)
        | apply (in_union_get_5 H) ] in
  first [ go tt
        | rewrite <- (for_set_union_empty_r B);
          repeat rewrite <- for_set_union_assoc;
          go tt ]
  end end.

Hint Extern 3 (_ \in _ \u _) => in_union_get.

Section InUnionExtract.
Variables (A:Type).
Implicit Types l : set A.

Lemma in_union_extract_1 : forall x l1,
  x \in (\{x} \u l1).
Proof using. intros. apply in_union_get_1. apply in_single_self. Qed.

Lemma in_union_extract_2 : forall x l1 l2,
  x \in (l1 \u \{x} \u l2).
Proof using. intros. apply in_union_get_2. apply in_single_self. Qed.

Lemma in_union_extract_3 : forall x l1 l2 l3,
  x \in (l1 \u l2 \u \{x} \u l3).
Proof using. intros. apply in_union_get_3. apply in_single_self. Qed.

Lemma in_union_extract_4 : forall x l1 l2 l3 l4,
  x \in (l1 \u l2 \u l3 \u \{x} \u l4).
Proof using. intros. apply in_union_get_4. apply in_single_self. Qed.

Lemma in_union_extract_5 : forall x l1 l2 l3 l4 l5,
  x \in (l1 \u l2 \u l3 \u l4 \u \{x} \u l5).
Proof using. intros. apply in_union_get_5. apply in_single_self. Qed.

End InUnionExtract.

Ltac in_union_extract :=
  match goal with |- ?x \in ?A =>
  match A with context [\{x}] =>
  let go tt := first
        [ apply (in_union_extract_1)
        | apply (in_union_extract_2)
        | apply (in_union_extract_3)
        | apply (in_union_extract_4)
        | apply (in_union_extract_5) ] in
  first [ go tt
        | rewrite <- (for_set_union_empty_r A);
          repeat rewrite <- for_set_union_assoc;
          go tt ]
  end end.

Hint Extern 3 (_ \in _) => in_union_extract.


(* ---------------------------------------------------------------------- *)
(** ** Tactics to invert a membership hypothesis *)

(* TODO: document and clean up *)

Section InversionsTactic.
Context (A:Type).
Implicit Types l : set A.
Implicit Types x : A.
Lemma empty_eq_single_inv_1 : forall x l1 l2,
  l1 = l2 -> x \notin l1 -> x \in l2 -> False.
Proof using. intros. subst*. Qed.
Lemma empty_eq_single_inv_2 : forall x l1 l2,
  l1 = l2 -> x \notin l2 -> x \in l1 -> False.
Proof using. intros. subst*. Qed.
Lemma notin_empty : forall x,
  x \notin (\{}:set A).
Proof using. intros. unfold notin. rewrite in_empty_eq. auto. Qed.
End InversionsTactic.
Hint Resolve notin_empty.

Ltac in_union_meta :=
  match goal with
  | |- _ \in \{_} => apply in_single_self
  | |- _ \in \{_} \u _ => apply in_union_l; apply in_single_self
  | |- _ \in _ \u _ => apply in_union_r; in_union_meta
  end.

Ltac fset_inv_core_for H :=
  let go L :=
     false L; [ apply H
              | try apply notin_empty
              | instantiate; try in_union_meta ] in
  match type of H with
  | \{} = _ => go empty_eq_single_inv_1
  | _ = \{} => go empty_eq_single_inv_2
  | _ = _ => go empty_eq_single_inv_1
  end.

Tactic Notation "fset_inv" constr(H) :=
  fset_inv_core_for H.

Ltac fset_inv_core :=
  match goal with
  | |- \{} <> _ => let H := fresh in intro H; fset_inv H
  | |- _ <> \{} => let H := fresh in intro H; fset_inv H
  | H: \{} = _ |- _ => fset_inv H
  | H: _ = \{} |- _ => fset_inv H
  end.

Tactic Notation "fset_inv" :=
  fset_inv_core.

Section InUnionInv.
Variables (A:Type).
Implicit Types l : set A.

Lemma set_in_empty_inv : forall x,
  x \in (\{}:set A) -> False.
Proof using. introv. apply notin_empty. Qed.
Lemma set_in_single_inv : forall x y : A,
  x \in (\{y}:set A) -> x = y.
Proof using. intros. rewrite @in_single_eq in H. auto. typeclass. Qed.
Lemma set_in_union_inv : forall x l1 l2,
  x \in (l1 \u l2) -> x \in l1 \/ x \in l2.
Proof using. introv H. rewrite @in_union_eq in H. auto. typeclass. Qed.

End InUnionInv.

Arguments set_in_single_inv [A] [x] [y].
Arguments set_in_union_inv [A] [x] [l1] [l2].


Ltac set_in_inv_base H M :=
  match type of H with
  | _ \in \{} => false; apply (@set_in_empty_inv _ _ H)
  | _ \in \{_} =>
    generalize (set_in_single_inv H); try clear H; intro_subst
  | _ \in _ \u _ =>
    let H' := fresh "TEMP" in
    destruct (set_in_union_inv H) as [H'|H'];
    try clear H; set_in_inv_base H' M
  | _ => rename H into M
  end.

Tactic Notation "set_in" constr(H) "as" ident(M) :=
  set_in_inv_base H M.
Tactic Notation "set_in" constr(H) :=
  let M := fresh "H" in set_in H as M.


(* ---------------------------------------------------------------------- *)
(** ** Tactic to prove two sets equal by double-inclusion *)

(* DEPRECATED: use "set_prove" instead when possible *)

Tactic Notation "eq_set" :=
  let H := fresh "TEMP" in
  apply set_ext; iff H; set_in H; in_union_get.
Tactic Notation "eq_set" "*" :=
  eq_set; auto_star.




(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)

(* FUTURE

  (** Sets of sets *)

  (* todo: typeclass for bigunion and bigintersection *)

  Definition bigunion_impl A (E : set (set A)) : set A :=
    \set{ x | exists_ F \in E, x \in (F:set A) }.

  Definition biguinter_impl A (E : set (set A)) : set A :=
    \set{ x | forall_ F \in E, x \in (F:set A) }.

*)



(************************************************************)
(************************************************************)
(************************************************************)
(* LibMap *)

(* ---------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------- *)

(* migration:

  map_split ==> split_restrict_remove
  map_split ==> split_restrict_remove_single
  map_index_def ==> index_def
  map_indom_update_already => LibMap.indom_update_already
  map_indom_update_inv => LibMap.indom_update_inv
  map_restrict_single ==> restrict_single
  map_update_restrict ==> update_remove_one_eq
  dom_restrict_in ==> index_remove_one_in
  restrict_read ==> remove_one_read_neq
  restrict_update ==> remove_one_update_neq

  map_indom_update => indom_update
  map_indom_update_self => indom_update_self
  binds_inv => rewrite binds_def
  binds_get => binds_read

  map_update_read_eq => update_read_eq
  map_update_read_neq => update_read_neq
  map_update_read_if => update_read_if

  dom_update_in => dom_update_index
  dom_update_in_variant => dom_update_index'
  dom_update_notin => dom_update
  map_update_as_union => update_def_union
  map_indom_update_already_inv => indom_update_already_inv

  reduce_ => fold_

*)


(* LATER: is this deprecated?
  Lemma binds_update_rem : forall A i j `{Inhab B} v w (M:map A B),
    j \notindom' M -> binds (M[j:=w]) i v -> binds M i v.
  Hint Resolve binds_update_rem.
*)


Lemma binds_update_indom_eq :
  forall A B (M : map A B) a1 a2 b1 b2,
  binds (M[a1:=b1]) a2 b2 =
  (    (a2 <> a1 /\ binds M a2 b2) 
    \/ (a2 = a1 /\ b2 = b1)).
Proof using.
  split. introv [ [ ? ? ] | [ ? ? ] ].
  { eauto using binds_update_neq. }
  { subst. eapply binds_update_eq. }
  { eauto using binds_update_analysis. }
Qed.


(* ---------------------------------------------------------------------- *)

(* LATER: cleanup the three lemmas below *)

(* FALSE
Lemma binds_update_neq_inv' : forall A B i j v w (M:map A B),
  binds (M[j:=w]) i v -> j \notindom M -> binds M i v.

Lemma binds_update_neq_eq : forall A `{Inhab B} i j v w (M:map A B),
  j \notindom M ->
  (binds M i v = binds (M[j:=w]) i v).
Proof using.
  split; intros.
  { eapply binds_update_neq; [ | eauto ].
    assert (i \indom M). { eapply index_of_binds; eauto. }
    intro. subst. unfold notin in *. tauto. }
  { eauto using binds_update_neq_inv'. }
Qed.

*)



Lemma binds_update_neq' : forall A i j `{Inhab B} v w (M:map A B), (* todo: needed? *)
  i <> j -> 
  binds M i v -> 
  binds (M[j:=w]) i v.
Proof using. intros. applys* binds_update_neq. Qed.



(* --TODO: deprecated? *)
Lemma dom_update_at_index' :
  forall A `{Inhab B} (M M' : map A B) (D : set A) x v,
  M' = M[x:=v] ->
  D = dom M ->
  x \in D ->
  D = dom M'.
Proof using. intros. subst. rewrite~ dom_update_at_index. Qed.

(* Hint Resolve index_of_indom. *)




(*-- TODO: this statement is temporary; we probably shouldn't use [Proper]. *)
Lemma fold_pointwise :
  forall B (m : monoid_op B) (leB : B -> B -> Prop),
  Monoid m ->
  refl leB ->
  Proper (leB ++> leB ++> leB) (monoid_oper m) ->
  forall A (E : set A),
  finite E ->
  forall (f f' : A -> B),
  (forall x, x \in E -> leB (f x) (f' x)) ->
  leB (fold m f E) (fold m f' E).
Proof using.
  intros. do 2 rewrite fold_eq_fold_to_list.
  applys~ LibList.fold_pointwise.
  intros x. forwards~ (_&EQ): finite_list_repr E. rewrite (EQ x). auto.
Qed.



Lemma foreach_remove_of_foreach_pred_incl : forall P Q E F,
  foreach P E -> 
  pred_incl P (fun (x:A) => x \notin F -> Q x) ->
  foreach Q (E \- F).
Proof using. introv M H Px. rewrite in_remove_eq in Px. applys* H. Qed.



(* ---------------------------------------------------------------------- *)
(** [to_set] *)

Lemma list_repr_to_set:
  forall A (xs : list A),
  noduplicates xs ->
  list_repr (to_set xs) xs.
Proof using.
  unfold list_repr, to_set. induction 1; split.
  { econstructor. }
  { tauto. }
  { econstructor; eauto. }
  { tauto. }
Qed.

Lemma list_repr_to_set_inverse:
  forall A (E : set A) (xs : list A),
  list_repr E xs ->
  E = to_set xs.
Proof using.
  unfold list_repr, to_set. introv (_ & ?).
  generalize dependent E. generalize dependent xs.
  induction xs; introv H; rewrite set_ext_eq; intros x;
  rewrite in_set_st_eq; rewrite H; tauto.
Qed.

Lemma to_set_nil:
  forall A,
  to_set (@nil A) = \{}.
Proof using.
  intros.
  erewrite <- list_repr_to_set_inverse by eapply list_repr_nil.
  eauto.
Qed.

(* -- TODO, fix using Prefix library

Lemma prefix_to_set:
  forall A (xs ys : list A),
  prefix xs ys ->
  to_set xs \c to_set ys.
Proof using.
  unfold to_set. introv (zs&?). subst.
  rewrite set_incl_in_eq. intros. rewrite in_set_st_eq in *.
  rewrite Mem_app_or_eq. tauto.
Qed.

*)

*)

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

Lemma div2_lt : forall n m, m <= n -> n > 0 -> div2 m < n.
Proof using. (* using stdlib *)
  nat_comp_to_peano. introv Le Gt.
  forwards: Nat.div2_decr m (n-1). omega. omega.
Qed.

Lemma div2_grows : forall n m, m <= n -> div2 m <= div2 n.
Proof using.
  nat_comp_to_peano.
  induction n using peano_induction. introv Le.
  destruct~ m. simpl. omega.
  destruct~ n. simpl. omega.
  destruct~ m. simpl. omega.
  destruct~ n. simpl. omega.
  simpl. rew_nat. apply~ H. nat_math. nat_math.
Qed.


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

Record order_wrt (A:Type) (E:binary A) (R:binary A) : Prop := {
   order_wrt_refl : refl R;
   order_wrt_trans : trans R;
   order_wrt_antisym : antisym_wrt E R }.



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

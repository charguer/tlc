
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
(* * Parity function *)



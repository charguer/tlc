(**************************************************************************
* TLC: A library for Coq                                                  *
* Infinite streams                                                        *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
From TLC Require Import LibTactics LibLogic LibInt LibList LibRelation LibWf.


(* ********************************************************************** *)
(** * Construction of streams *)

(* ---------------------------------------------------------------------- *)
(** ** Definition *)

CoInductive stream (A:Type) : Type :=
  | stream_intro : A -> stream A -> stream A.

Notation "x ::: s" := (stream_intro x s) (at level 35).


(* ---------------------------------------------------------------------- *)
(** ** Projections *)

Definition stream_head A (s:stream A) :=
  let '(x:::s') := s in x.

Definition stream_tail A (s:stream A) :=
  let '(x:::s') := s in s'.


(* ---------------------------------------------------------------------- *)
(** ** Basic operations *)

(** Constant stream *)

CoFixpoint const A (x:A) : stream A :=
  x:::(const x).

(** List obtained by cutting a stream at length [n] *)

Fixpoint take A (n:nat) (s:stream A) : list A :=
  match n with
  | O => nil
  | S n' => let '(x:::s') := s in x::(take n' s')
  end.

(** Mapping of a function on values from a stream *)

CoFixpoint map A B (f:A->B) (s:stream A) : stream B :=
  let '(x:::s') := s in f x ::: (map f s').

(** N-th element of a stream *)

Fixpoint nth A (n:nat) (s:stream A) : A :=
  let '(x:::s') := s in
  match n with
  | O => x
  | S n' => nth n' s'
  end.

(** Streams are inhabited *)

#[global]
Instance Inhab_stream : forall `{Inhab A}, Inhab (stream A).
Proof using. intros. apply (Inhab_of_val (const arbitrary)). Qed.


(* ---------------------------------------------------------------------- *)
(** ** Diagonal stream *)

(** Diagonal stream constructed from a sequence of streams *)

CoFixpoint diagonal A (u:nat->stream A) (n:nat) : stream A :=
  (nth n (u n)):::(diagonal u (S n)).

(** Description of the [n]-th element of a diagonal stream *)

Lemma stream_diagonal_nth : forall A (u:nat->stream A) n k,
  nth n (diagonal u k) = nth ((n+k)%nat) (u (n+k)%nat).
Proof using.
  intros. gen k. induction n; intros.
  simple~.
  math_rewrite ((S n + k)%nat = (n + (S k))%nat). rewrite~ <- IHn.
Qed.


(* ********************************************************************** *)
(** * Bisimilarity *)

(* ---------------------------------------------------------------------- *)
(** ** Definition of bisimilarity *)

(** Bisimilarity modulo [E] *)

CoInductive bisimilar_mod (A:Type) (E:binary A) : binary (stream A) :=
  | bisimilar_mod_intro : forall x1 x2 s1 s2,
      E x1 x2 ->
      bisimilar_mod E s1 s2 ->
      bisimilar_mod E (x1:::s1) (x2:::s2).

(** Bisimilarity modulo Leibnitz *)

Definition bisimilar (A:Type) := bisimilar_mod (@eq A).

Notation "x === y" := (bisimilar x y) (at level 68).

(** Bisimilarity is an equivalence *)

Lemma equiv_bisimilar_mod : forall A (E:binary A),
  equiv E ->
  equiv (bisimilar_mod E).
Proof using.
  introv Equiv. constructor.
  unfolds. cofix IH. destruct x. constructor; dauto.
  unfolds. cofix IH. destruct x; destruct y; introv M.
   inversions M. constructor; dauto.
  unfolds. cofix IH. destruct x; destruct y; destruct z; introv M1 M2.
   inversions M1. inversions M2. constructor; dauto.
Qed.

Lemma equiv_bisimilar : forall A,
  equiv (@bisimilar A).
Proof using. intros. apply~ equiv_bisimilar_mod. applys equiv_eq. Qed.


(* ---------------------------------------------------------------------- *)
(* ** List similarity modulo equivalence *)

(** [list_equiv E l1 l2] asserts that the lists [l1] and [l2]
    are equal when their elements are compared modulo E *)

Definition list_equiv (A:Type) (E:binary A) : binary (list A) :=
   Forall2 E.

Section ListEquiv.
Hint Constructors Forall2.

Lemma equiv_list_equiv : forall A (E:binary A),
  equiv E ->
  equiv (list_equiv E).
Proof using.
  introv Equiv. unfold list_equiv. constructor.
  unfolds. induction x. auto. constructor; dauto.
  unfolds. induction x; destruct y; introv H; inversions H; dauto.
  unfolds. induction y; destruct x; destruct z; introv H1 H2;
   inversions H1; inversions H2; dauto.
Qed.

End ListEquiv.


(* ---------------------------------------------------------------------- *)
(** ** Bisimilarity up to a given index *)

(** Bisimilarity modulo [E] up to index [n] *)

Definition bisimilar_mod_upto A (E:binary A) n s1 s2 :=
  list_equiv E (take n s1) (take n s2).

Section Bisimilar.
Hint Unfold list_equiv.
Hint Constructors Forall2.

(** This relation is an equivalence *)

Lemma equiv_bisimilar_mod_upto : forall A (E:binary A) n,
  equiv E ->
  equiv (bisimilar_mod_upto E n).
Proof using.
  introv Equiv. unfold bisimilar_mod_upto.
  lets: (equiv_list_equiv Equiv). constructor; unfolds; dauto.
Qed.

(** Bisimilarity implies bisimilarity at any index *)

Lemma bisimilar_mod_to_upto : forall A (E:binary A) n s1 s2,
  bisimilar_mod E s1 s2 -> bisimilar_mod_upto E n s1 s2.
Proof using.
  unfold bisimilar_mod_upto.
  induction n; introv H. simple~.
  destruct s1; destruct s2; simpls. inversions H. constructor~. apply~ IHn.
Qed.

(** Bisimilarity at any index imply bisimilarity *)

Lemma bisimilar_mod_take : forall A (E:binary A) s1 s2,
  (forall i, list_equiv E (take i s1) (take i s2)) ->
  bisimilar_mod E s1 s2.
Proof using.
  intros A E. cofix IH. intros.
  destruct s1 as [x1 s1]. destruct s2 as [x2 s2]. constructor.
    lets_inverts (H 1%nat). auto.
    apply IH. intros i. lets_inverts (H (S i)). auto.
Qed.

(** Bisimilarity up to index zero always holds *)

Lemma bisimilar_mod_upto_zero : forall A (E:binary A) s1 s2,
  bisimilar_mod_upto E 0%nat s1 s2.
Proof using. intros; hnf; simple~. Qed.

(** Bisimilarity up to [S n] from bisimilarity up to [n]
    and equality between n-th elements *)

Lemma bisimilar_mod_upto_succ : forall A (E:binary A) n s1 s2,
  equiv E ->
  bisimilar_mod_upto E n s1 s2 ->
  nth n s1 = nth n s2 ->
  bisimilar_mod_upto E (S n) s1 s2.
Proof using.
  introv Equiv Bis Equ. unfolds bisimilar_mod_upto.
  gen s1 s2. induction n; intros; destruct s1; destruct s2.
  simpls. subst. constructor; dauto.
  set_eq m: (S n). simpls.
  inversions Bis. constructor~. apply~ IHn.
Qed.

End Bisimilar.

#[global]
Hint Resolve equiv_bisimilar_mod_upto.
#[global]
Hint Resolve bisimilar_mod_upto_zero.


(* ********************************************************************** *)
(** * Properties of streams *)

(** [eventually P s] holds if [s] contains a value satisfying [P] *)

Inductive eventually A (P:A->Prop) : stream A -> Prop :=
  | eventually_head : forall x s,
      P x -> eventually P (x:::s)
  | eventually_tail : forall x s,
      eventually P s -> eventually P (x:::s).

(** [always P s] holds if every substream of [s] satisfies [P] *)

CoInductive always A (P:stream A -> Prop) : stream A -> Prop :=
  | always_intro : forall s x,
      always P s -> P (x:::s) -> always P (x:::s).

(** [infinitely_often P s] holds if the stream [s] contains
    infinitely many values satisfying [P] *)

Definition infinitely_often A (P:A->Prop) :=
  always (eventually P).

(** [first_st P s n] holds if the first element of [s] satisfying
    [P] is found at index [n] *)

Fixpoint first_st_at A (P:A->Prop) (s:stream A) (n:nat) :=
  let '(x:::s') := s in
  match n with
  | O => P x
  | S n' => ~ P x /\ first_st_at P s' n'
  end.

(** [first_st] is a functional relation; there is at most
    one index [n] such that [first_st_at P s n] holds *)

Lemma first_st_at_inj : forall n1 n2 A (P:A->Prop) s,
  first_st_at P s n1 ->
  first_st_at P s n2 ->
  n1 = n2.
Proof using.
  induction n1; destruct n2; destruct s; simpl; introv H1 H2.
  auto. destruct H2. false. destruct H1. false.
  destruct H1. destruct H2. fequals. apply* IHn1.
Qed.

Arguments first_st_at_inj [n1] [n2] [A] [P] [s].



(**************************************************************************
* TLC: A library for Coq                                                  *
* Minimum w.r.t. an order relation                                        *
**************************************************************************)

Set Implicit Arguments.
Require Import LibTactics LibLogic LibReflect LibOperation
  LibRelation LibOrder LibEpsilon.
Generalizable Variables A.

(* This module offers the functions [mmin] and [mmax] which produce
   the minimum and maximum elements of a non-empty, bounded set. *)

(* TODO: rename mmin to min and mmax to max *)


(**************************************************************************)
(* * Lower bound and minimum*)

(* [lower_bound le P x] means that [x] is a lower bound for the
   set [P] with respect to the ordering [le]. *)

Definition lower_bound (A:Type) (le:binary A) (P:A->Prop) (x:A) :=
  forall y, P y -> le x y.

(* [min_element le P x] means that [x] is a minimal element of
   [P], i.e., it is both a member of [P] and a lower bound for
   [P]. *)

Definition min_element (A:Type) (le:binary A) (P:A->Prop) (x:A) :=
  P x /\ lower_bound le P x.

(* [mmin le P] is a minimal element of [P] with respect to [le],
   when such an element exists. *)

Definition mmin `{Inhab A} (le:binary A) (P:A->Prop) :=
  epsilon (min_element le P).


(**************************************************************************)
(* * Upper bound and maximum *)

(* [upper_bound le P x] means that [x] is a lower bound for the
   set [P] with respect to the ordering [le]. *)

Definition upper_bound (A:Type) (le:binary A) (P:A->Prop) (x:A) :=
  forall y, P y -> le y x.

(* [max_element le P x] means that [x] is a maximal element of
   [P], i.e., it is both a member of [P] and a lower bound for
   [P]. *)

Definition max_element (A:Type) (le:binary A) (P:A->Prop) (x:A) :=
  P x /\ upper_bound le P x.

(* [mmax le P] is a minimal element of [P] with respect to [le],
   when such an element exists. *)

Definition mmax `{Inhab A} (le:binary A) (P:A->Prop) :=
  epsilon (max_element le P).


(**************************************************************************)
(* * Least upper bound and greatest lower bound *)

(* [lub le P x] means that [x] is a least upper bound
   for the set [P] with respect to the ordering [le]. *)

Definition lub A (le:binary A) (P:A->Prop) (x:A) :=
  min_element le (upper_bound le P) x.

(* [glb le P x] means that [x] is a greatest lower bound
   for the set [P] with respect to the ordering [le]. *)

Definition glb A (le:binary A) (P:A->Prop) (x:A) :=
  min_element le (lower_bound le P) x.


(**************************************************************************)
(* * Connexion between lower and bounds *)

Lemma upper_bound_flip : forall A (le:binary A),
  upper_bound le = lower_bound (flip le).
Proof using.
  extens. intros P x. unfolds lower_bound, upper_bound. iff*.
Qed.

Lemma max_element_flip : forall A (le:binary A) (P:A->Prop) (x:A),
  max_element le P x = min_element (flip le) P x.
Proof using.
  extens. unfold max_element, min_element. rewrite* upper_bound_flip.
Qed.

Lemma mmax_flip : forall `{Inhab A} (le:binary A) (P:A->Prop),
  mmax le P = mmin (flip le) P.
Proof using.
  intros. applys epsilon_eq. intros x. rewrite* max_element_flip.
Qed.


(**************************************************************************)
(* * Elimination roperties *)

(* [bounded_has_minimal le] means that, at type [A], it is
   the case that every non-empty set that admits a lower
   bound has a minimal element. *)

Definition bounded_has_minimal (A:Type) (le:binary A) :=
  (* Recall that [ex P] means that [P] has an inhabitant; i.e.,
     it is equivalent to [exists x, P x]. *)
  forall P,
  ex P ->
  ex (lower_bound le P) ->
  ex (min_element le P).


(* If the set [P] is non-empty and admits a lower bound, and if the type
   [A] is such that every such set has a minimal element, then [P] has a
   minimal element, and this element is [mmin le P]. *)

Lemma mmin_spec : forall `{Inhab A} (le:binary A) (P:A->Prop) m,
  m = mmin le P ->
  ex P ->
  ex (lower_bound le P) ->
  bounded_has_minimal le ->
  min_element le P m.
Proof using.
  intros. subst. unfold mmin. spec_epsilon* as m.
Qed.



(**************************************************************************)
(* * Application to [nat] *)

Require Import LibNat.

(* The type [nat] enjoys this property. *)

Lemma increment_lower_bound_nat : forall (P : nat->Prop) x,
  lower_bound le P x ->
  ~ P x ->
  lower_bound le P (x + 1)%nat.
Proof using.
  introv hlo ?. intros y ?.
  destruct (eq_nat_dec x y).
    { subst. tauto. }
    { forwards: hlo; eauto. nat_math. }
Qed.

Lemma bounded_has_minimal_nat :
  @bounded_has_minimal nat le.
Proof using.
  (* Assume a set [P], such that [y] is an inhabitant of [P]
     and [x] is a lower bound for [P]. *)
  intros P [ y ? ].
  (* We reason by induction on the difference [y + 1 - x].
     Reasoning with [y - x] would work too, but this choice
     is more elegant, as it makes the base case a contradiction,
     and avoids a little duplication. *)
  cut (
    forall (k x : nat), (y + 1 - x)%nat = k ->
    lower_bound le P x ->
    exists z, min_element le P z
  ). { intros ? [ x ? ]. eauto. }
  induction k; introv ? hlo.
  (* Base. *)
  (* Our hypotheses imply that [x] must be less than or equal to
     [y]. Because in this case the difference [y + 1 - x] is zero,
     this leads to a contradiction. *)
  { false. forwards: hlo; eauto. nat_math. }
  (* Step. *)
  (* Eeither [P x] holds, or it does not. If it does, then [x]
     is the desired minimal element. If it does not, this implies
     that [x + 1] is a lower bound for [P], and the induction
     hypothesis can be used. *)
  destruct (classic (P x)).
    { exists x. split; eauto. }
    { eapply (IHk (x + 1)%nat). nat_math. eauto using increment_lower_bound_nat. }
Qed.

Hint Resolve bounded_has_minimal_nat : bounded_has_minimal.

(* Furthermore, at type [nat], every set admits a lower bound. *)

Lemma admits_lower_bound_nat : forall (P : nat->Prop),
  ex (lower_bound le P).
Proof using.
  exists 0%nat. unfold lower_bound. nat_math.
Qed.

Hint Resolve admits_lower_bound_nat : admits_lower_bound.

(* At type [nat], every non-empty set that admits an upper bound
   has a maximal element. *)

Lemma bounded_has_maximal_nat :
  @bounded_has_minimal nat (flip le).
Proof using.
  (* Assume a set [P], such that [y] is an inhabitant of [P]
     and [x] is an upper bound for [P]. *)
  intros P [ y ? ] [ x h ].
  assert (y <= x).
    { forwards: h. eauto. eauto. }
  (* We apply our previous result to the image of [P] through
     the function that maps [i] to [x - i]. (We note that this
     function is its own inverse.) This yields a minimal
     element [z] of this image. Thus, [x - z] is the desired
     maximal element of [P]. *)
  assert (self_inverse: forall i, i <= x -> (x - (x - i))%nat = i).
    intros. nat_math.
  forwards [ z [ ? hz ]]: (@bounded_has_minimal_nat (fun i => P (x - i)%nat)).
    { exists (x - y)%nat. rewrite self_inverse by eauto. eauto. }
    { eauto using admits_lower_bound_nat. }
  exists (x - z)%nat.
  clear dependent y.
  split; [ assumption | ].
  intros y ?.
  assert (y <= x).
    { forwards: h. eauto. eauto. }
  forwards: hz (x - y)%nat.
    { rewrite self_inverse by eauto. eauto. }
  unfold flip. nat_math.
Qed.

Hint Resolve bounded_has_maximal_nat : bounded_has_minimal.


Lemma mmin_spec_nat:
  forall (P:nat->Prop) m,
  m = mmin le P ->
  ex P ->
  P m /\ (forall x, P x -> m <= x).
Proof using.
  introv E Q. applys (@mmin_spec _ _ _ P m E Q).
  applys admits_lower_bound_nat.
  applys bounded_has_minimal_nat.
Qed.


(**************************************************************************)
(* * Typeclasses *)

(* [MMin P] is [mmin le P], in a context where the desired
   ordering can be inferred. *)

Definition MMin `{Inhab A} `{Le A} := mmin le.

(* [MMax P] is [mmax le P], in a context where the desired
   ordering can be inferred. *)

Definition MMax `{Inhab A} `{Le A} := mmax le.





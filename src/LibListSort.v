(*--under construction
(**************************************************************************
* TLC: A library for Coq                                                  *
* Sorted lists                                                            *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
From TLC Require Import LibTactics LibLogic LibRelation LibWf LibList
 LibOrder LibNat.


(* ********************************************************************** *)
(** * List permutation *)

(* ---------------------------------------------------------------------- *)
(** ** Definition *)

(** We consider a particular definition of [permut], but there would
    be many other equivalent definitions. Users of this library should
    not manipulate the definition directly, but instead work exclusively
    using the properties of [permut], established in this file. *)

Inductive permut_one (A:Type) : list A -> list A -> Prop :=
  | permut_one_intro : forall l1 l2 l3 l4,
      permut_one (l1++l2++l3++l4) (l1++l3++l2++l4).

Definition permut (A:Type) := rtclosure (@permut_one A).


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Section PermutProp.
Variables (A : Type).
Implicit Types l : list A.
Implicit Types P : A->Prop.

Hint Constructors permut_one.

(** Permutation is an equivalence *)

(* --TODO: use [refl] [sym] [trans] predicates *)

Lemma permut_refl : forall l,
  permut l l.
Proof using. intros. apply rtclosure_refl. Qed.

Lemma permut_sym : forall l1 l2,
  permut l1 l2 ->
  permut l2 l1.
Proof using.
  intros. unfold permut. gen l1 l2. applys rtclosure_ind_r.
  { apply permut_refl. }
  { intros. applys rtclosure'r_step. apply IHrtclosure. inverts~ H. }

Qed.

Lemma permut_sym_eq : forall l1 l2,
  permut l1 l2 = permut l2 l1.
Proof using. intros. hint permut_sym. extens*. Qed.

Lemma permut_trans : forall l2 l1 l3,
  permut l1 l2 ->
  permut l2 l3 ->
  permut l1 l3.
Proof using. intros. apply* rtclosure_trans. Qed.

(** Permutation is a congruence with respect to [++] *)

Lemma permut_app_l : forall l1 l1' l2,
  permut l1 l1' ->
  permut (l1 ++ l2) (l1' ++ l2).
Proof using.
  introv H. gen l2. induction H; intros.
  { apply permut_refl. }
  { specializes IHrtclosure l2. inverts H.
    rew_list in *. applys permut_trans.
    { applys* rtclosure_step. } { apply permut_refl. } }
Qed.

Lemma permut_app_r : forall l1 l2 l2',
  permut l2 l2' ->
  permut (l1 ++ l2) (l1 ++ l2').
Proof using.
  introv H. gen l1. induction H; intros.
  { apply permut_refl. }
  { specializes IHrtclosure l1. inverts H.
    rewrite <- app_assoc in *. applys permut_trans.
    { applys* rtclosure_step. } { apply permut_refl. } }
Qed.

Lemma permut_app_lr : forall l1 l1' l2 l2',
  permut l1 l1' ->
  permut l2 l2' ->
  permut (l1 ++ l2) (l1' ++ l2').
Proof using.
  intros. applys rtclosure_trans.
  { applys* permut_app_l. } { apply* permut_app_r. }
Qed.

Lemma permut_cons : forall x l1 l2,
  permut l1 l2 ->
  permut (x::l1) (x::l2).
Proof using.
  intros. lets: (@permut_app_r (x::nil) _ _ H). rew_list~ in *.
Qed.

Lemma permut_last : forall x l1 l2,
  permut l1 l2 ->
  permut (l1&x) (l2&x).
Proof using.
  intros. applys~ permut_app_lr. applys permut_refl.
Qed.

(** Other results *)

Lemma mem_permut_inv_r : forall l1 l2 x,
  mem x l1 ->
  permut l1 l2 ->
  mem x l2.
Proof using.
  introv M K. gen M. induction K as [|l2 l1 l3 H]; intros.
  { auto. }
  { inverts H. applys (rm IHK). repeat rewrite mem_app_eq in *. autos*. }
Qed.

Lemma mem_permut_inv_l : forall l1 l2 x,
  mem x l1 ->
  permut l2 l1 ->
  mem x l2.
Proof using.
  introv M K. hint permut_sym, mem_permut_inv_r. autos*.
Qed.

Lemma permut_flip : forall l1 l2,
  permut (l1 ++ l2) (l2 ++ l1).
Proof using.
  intros. lets: (permut_one_intro nil l1 l2 nil).
  rew_list in *. apply~ rtclosure_once.
Qed.

Lemma permut_rev : forall l,
  permut l (rev l).
Proof using.
  intros. induction l. apply permut_refl. rew_list.
  lets M: (@permut_flip (a::nil) (rev l)). rew_list in M.
  applys~ permut_trans M. apply~ permut_cons.
Qed.

Lemma Forall_permut_inv : forall P l1 l2,
  Forall P l1 ->
  permut l1 l2 ->
  Forall P l2.
Proof using.
  introv F K. rewrite Forall_eq_forall_mem in *.
  introv M. applys F. applys* mem_permut_inv_l M K.
Qed.  (* COQBUG? why [applys* mem_permut_inv_l] does not work *)

Lemma Exists_permut_inv : forall P l1 l2,
  Exists P l1 ->
  permut l1 l2 ->
  Exists P l2.
Proof using.
  introv. do 2 rewrite Exists_eq_exists_mem. intros (x&M&Px) K.
  hint mem_permut_inv_r. autos*.
Qed.  (* COQBUG? why [applys* mem_permut_inv_l] does not work *)

End PermutProp.

Hint Resolve permut_refl permut_flip permut_app_lr permut_cons
  permut_last permut_rev.


(* ---------------------------------------------------------------------- *)
(** ** Permutation tactic *)

(** [permut_simpl] simplifies a goal of the form
    [permut l l'] where [l] and [l'] are lists built with
    concatenation and consing, by cancelling syntactically
    equal elements. *)

Section PermutationTactic.
Variables (A : Type).
Implicit Types l : list A.

Lemma permut_get_1 : forall l1 l2,
  permut (l1 ++ l2) (l1 ++ l2).
Proof using. intros. apply permut_refl. Qed.

Lemma permut_get_2 : forall l1 l2 l3,
  permut (l1 ++ l2 ++ l3) (l2 ++ l1 ++ l3).
Proof using.
  intros. apply rtclosure_once.
  applys (@permut_one_intro _ nil l1 l2 l3).
Qed.

Lemma permut_get_3 : forall l1 l2 l3 l4,
  permut (l1 ++ l2 ++ l3 ++ l4) (l2 ++ l3 ++ l1 ++ l4).
Proof using.
  intros. do 2 rewrite <- (@app_assoc _ l2).
  apply permut_get_2.
Qed.

Lemma permut_get_4 : forall l1 l2 l3 l4 l5,
  permut (l1 ++ l2 ++ l3 ++ l4 ++ l5)
         (l2 ++ l3 ++ l4 ++ l1 ++ l5).
Proof using.
  intros. do 2 rewrite <- (@app_assoc _ l2).
  apply permut_get_3.
Qed.

Lemma permut_get_5 : forall l1 l2 l3 l4 l5 l6,
  permut (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6)
         (l2 ++ l3 ++ l4 ++ l5 ++ l1 ++ l6).
Proof using.
  intros. do 2 rewrite <- (@app_assoc _ l2).
  apply permut_get_4.
Qed.

Lemma permut_get_6 : forall l1 l2 l3 l4 l5 l6 l7,
  permut (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l7)
         (l2 ++ l3 ++ l4 ++ l5 ++ l6 ++ l1 ++ l7).
Proof using.
  intros. do 2 rewrite <- (@app_assoc _ l2).
  apply permut_get_5.
Qed.

Lemma permut_tactic_setup : forall l1 l2,
  permut (nil ++ l1 ++ nil) (l2 ++ nil) -> permut l1 l2.
Proof using. intros. rew_list~ in H. Qed.

Lemma permut_tactic_keep : forall l1 l2 l3 l4,
  permut ((l1 ++ l2) ++ l3) l4 ->
  permut (l1 ++ (l2 ++ l3)) l4.
Proof using. intros. rew_list~ in H. Qed.

Lemma permut_tactic_simpl : forall l1 l2 l3 l4,
  permut (l1 ++ l3) l4 ->
  permut (l1 ++ (l2 ++ l3)) (l2 ++ l4).
Proof using.
  intros. eapply permut_trans.
  apply permut_get_2. apply~ permut_app_r.
Qed.

Lemma permut_tactic_trans : forall l1 l2 l3,
  permut l3 l2 -> permut l1 l3 -> permut l1 l2.
Proof using. introv P1 P2. apply~ (permut_trans P2 P1). Qed.

End PermutationTactic.

(** [permut_prepare] applies to a goal of the form [permut l l']
    and sets [l] and [l'] in the form [l1 ++ l2 ++ .. ++ nil],
    (some of the lists [li] are put in the form [x::nil]). *)
(* --TODO: improve so as to ensure no rewrite inside elements *)

Hint Rewrite app_assoc app_nil_l app_nil_r : permut_rew.

Ltac permut_lemma_get n :=
  match number_to_nat n with
  | 1 => constr:(permut_get_1)
  | 2 => constr:(permut_get_2)
  | 3 => constr:(permut_get_3)
  | 4 => constr:(permut_get_4)
  | 5 => constr:(permut_get_5)
  end.

Ltac permut_isolate_cons :=
  do 20 try (* --TODO : repeat *)
    match goal with |- context [?x::?l] =>
      match l with
      | nil => fail 1
      | _ => rewrite <- (@app_cons_one_r _ x l)
      end
    end.

Ltac permut_simpl_prepare :=
   autorewrite with permut_rew;
   permut_isolate_cons;
   autorewrite with permut_rew;
   apply permut_tactic_setup;
   repeat rewrite app_assoc.

Ltac permut_index_of l lcontainer :=
  match constr:(lcontainer) with
  | l ++ _ => constr:(1)
  | _ ++ l ++ _ => constr:(2)
  | _ ++ _ ++ l ++ _ => constr:(3)
  | _ ++ _ ++ _ ++ l ++ _ => constr:(4)
  | _ ++ _ ++ _ ++ _ ++ l ++ _ => constr:(5)
  | _ ++ _ ++ _ ++ _ ++ _ ++ l ++ _ => constr:(6)
  | _ => constr:(0) (* not found *)
  end.

Ltac permut_simpl_once :=
  match goal with
  | |- permut (_ ++ nil) _ => fail 1
  | |- permut (_ ++ (?l ++ _)) ?l' =>
     match permut_index_of l l' with
     | 0 => apply permut_tactic_keep
     | ?n => let F := permut_lemma_get n in
            eapply permut_tactic_trans;
            [ apply F
            | apply permut_tactic_simpl ]
     end
  end.

Ltac permut_simpl :=
  permut_simpl_prepare;
  repeat permut_simpl_once;
  autorewrite with permut_rew;
  try apply permut_refl.



(* ********************************************************************** *)
(** * Sorted lists *)

(* ---------------------------------------------------------------------- *)
(** ** [heads_le] *)

(** [head_le x l] asserts that the head of [l], if any, is smaller
    than [x] w.r.t. [le]. It will be useful to state lemmas about [sorted]. *)

Definition head_le A (le : binary A) x l :=
  match l with
  | nil => True
  | h::_ => le x h
  end.

Section HeadLe.
Variables (A : Type) (le : binary A).
Implicit Types l : list A.

Lemma head_le_trans : forall x y l,
  trans le ->
  head_le le x l ->
  le y x ->
  head_le le y l.
Proof using.
  introv Tr H L. destruct l; simpls. { auto. } { applys* Tr. }
Qed.

Lemma Forall_le_head_le : forall x l,
  Forall (le x) l ->
  head_le le x l.
Proof using. introv H. destruct l; simpls. auto. inverts~ H. Qed.

End HeadLe.


(* ---------------------------------------------------------------------- *)
(** ** Properties of [sorted] *)

(** [sorted le l] asserts that [l] is sorted w.r.t. [le] *)

Inductive sorted A (le : binary A) : list A -> Prop :=
  | sorted_nil :
      sorted le nil
  | sorted_one : forall x,
      sorted le (x::nil)
  | sorted_two : forall x y l,
      sorted le (y::l) ->
      le x y ->
      sorted le (x::y::l).

Section Sorted.
Variables (A : Type) (le : binary A).
Hint Constructors sorted.

(** Constructor: if [l] is sorted and [x] is smaller than the head
   of [l], then [x::l] is sorted. *)

Lemma sorted_cons : forall l x,
  sorted le l ->
  head_le le x l ->
  sorted le (x::l).
Proof using. introv S Hd. inverts~ S. Qed.

(** Inversion *)

Lemma sorted_cons_inv : forall x l,
  sorted le (x::l) ->
  head_le le x l /\ sorted le l.
Proof using. introv H. inverts H; simpls~. Qed.

Lemma sorted_cons_inv_head_le : forall x l,
  sorted le (x::l) ->
  head_le le x l.
Proof using. introv H. inverts H; simpls~. Qed.

Lemma sorted_cons_inv_sorted : forall x l,
  sorted le (x::l) ->
  sorted le l.
Proof using. introv H. inverts~ H. Qed.

(** Key lemma: if [l] is sorted and [x] is smaller than the
   head of [l], then [x] is smaller than all elements in [l]. *)

Lemma Forall_le_of_sorted_head_le : forall x l,
  trans le ->
  sorted le l ->
  head_le le x l ->
  Forall (le x) l.
Proof using.
  intros x l. induction l; introv Tr S L.
  { constructor~. }
  { simpls. lets (N&M): (sorted_cons_inv S). constructor~. apply~ IHl.
    applys* head_le_trans. }
Qed.

End Sorted.



(* ********************************************************************** *)
(** * Sorting of a list *)

(* ---------------------------------------------------------------------- *)
(** ** Definition *)

(** [sorts le l l'] asserts that [l'] is the result of sorting
    [l] w.r.t. [le]. *)

Definition sorts A (le : binary A) (l l' : list A) : Prop :=
  permut l l' /\ sorted le l'.


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Section Sorts.
Variables (A : Type).
Implicit Types le : binary A.
Hint Resolve sorted_nil sorted_one.

Lemma sorts_refl : forall le l,
  sorted le l ->
  sorts le l l.
Proof using. split. apply permut_refl. auto. Qed.

Lemma sorts_permut : forall l1 l2 l' le,
  sorts le l1 l' ->
  permut l2 l1 ->
  sorts le l2 l'.
Proof using.
  introv [P1 S1] Per. split~.
  apply* (@permut_trans _ l1).
Qed.

Lemma sorts_cons : forall le l l' x,
  sorts le l l' ->
  head_le le x l' ->
  sorts le (x::l) (x::l').
Proof using.
  introv [P S] Hd. split.
  { apply~ permut_cons. } { apply~ sorted_cons. }
Qed.

Lemma sorts_length_lt_2 : forall le l,
  length l < 2 ->
  sorts le l l.
Proof using.
  intros. apply sorts_refl. destruct~ l.
  destruct~ l. rew_list in *. false. nat_math.
Qed.

Lemma sorts_2 : forall le l x1 x2,
  permut l (x1::x2::nil) ->
  le x1 x2 ->
  sorts le l (x1::x2::nil).
Proof using.
  intros. apply~ (@sorts_permut (x1::x2::nil)).
  apply sorts_refl. apply~ sorted_cons.
Qed.

Lemma sorts_3 : forall le l x1 x2 x3,
  permut l (x1::x2::x3::nil) ->
  le x1 x2 ->
  le x2 x3 ->
  sorts le l (x1::x2::x3::nil).
Proof using.
  intros. apply~ (@sorts_permut (x1::x2::x3::nil)).
  apply sorts_refl. apply~ sorted_cons.
  apply~ sorted_cons.
Qed.

End Sorts.



(* ********************************************************************** *)
(** * Sorting of a list in reverse order *)

(* ---------------------------------------------------------------------- *)
(** ** [heads_le] *)

(** [heads_le l1 l2] asserts that the head of [l1], if any, is smaller
    than the head of [l2], if any. This auxiliary definition is very
    useful for reasoning about merge-sort style algorithms,
    especially those involving lists sorted in reverse order (see below). *)

Definition heads_le A (le : binary A) l1 l2 :=
  match l1,l2 with
  | _,nil => True
  | nil,_ => True
  | h1::_,h2::_ => le h1 h2
  end.

Section HeadsLe.
Variables (A : Type).
Variable le : binary A.
Hint Resolve sorted_nil sorted_one.

(** Rewriting *)

Lemma heads_le_cons_l : forall x l1 l2,
  heads_le le (x::l1) l2 = head_le le x l2.
Proof using. intros. destruct~ l2. Qed.

Lemma heads_le_cons_r : forall x l1 l2,
  heads_le le l1 (x::l2) = head_le le x l1.
Proof using. intros. destruct~ l1. Qed.

Lemma heads_le_nil_l : forall l,
  heads_le le nil l.
Proof using. intros. unfolds. destruct~ l. Qed.

Lemma heads_le_nil_r : forall l,
  heads_le le l nil.
Proof using. intros. unfolds. destruct~ l. Qed.

(** Simplification for flip *)

Lemma heads_le_flip_eq : forall l1 l2,
  heads_le (flip le) l1 l2 = heads_le le l2 l1.
Proof using. destruct l1; destruct l2; auto. Qed.

Lemma heads_le_flip : forall l1 l2,
  heads_le le l2 l1 ->
  heads_le (flip le) l1 l2.
Proof using. intros. rewrite~ heads_le_flip_eq. Qed.

Lemma heads_le_flip_inv : forall l1 l2,
  heads_le (flip le) l1 l2 ->
  heads_le le l2 l1.
Proof using. intros. rewrite~ <- heads_le_flip_eq. Qed.

End HeadsLe.


(* ---------------------------------------------------------------------- *)
(** ** [rsorted] *)

(** [rsorted le l] asserts that [l] is sorted in reverse order
    w.r.t. [le]. *)

Definition rsorted A (le : binary A) := sorted (flip le).

Section RSorted.
Variables (A : Type) (le : binary A).
Implicit Types l : list A.
Hint Constructors sorted.
Hint Resolve sorted_nil sorted_one.
Hint Unfold rsorted.

(** Constructors *)

Lemma rsorted_nil : rsorted le nil.
Proof using. applys sorted_nil. Qed.

Lemma rsorted_one : forall x,
  rsorted le (x::nil).
Proof using. intros. applys sorted_one. Qed.

Lemma rsorted_two : forall x y l,
  rsorted le (y::l) ->
  le y x ->
  rsorted le (x::y::l).
Proof using. intros. applys* sorted_two. Qed.

Lemma rsorted_cons : forall l x,
  rsorted le l ->
  head_le (flip le) x l ->
  rsorted le (x::l).
Proof using. introv S H. inverts~ S. Qed.

(** Inversion *)

Lemma rsorted_cons_inv : forall x l,
  rsorted le (x::l) ->
  head_le (flip le) x l /\ rsorted le l.
Proof using. introv H. inverts H; simpls~. Qed.

Lemma rsorted_cons_inv_head_le : forall x l1 l2,
  rsorted le (x::l2) ->
  head_le (flip le) x l2.
Proof using. introv E. forwards*: rsorted_cons_inv E. Qed.

End RSorted.

(** Append of a the reverse of a [rsorted] list and a [sorted] list. *)

Lemma sorted_app_rev : forall (A : Type) (le : binary A) l1 l2,
  heads_le le l1 l2 ->
  rsorted le l1 ->
  sorted le l2 ->
  sorted le ((rev l1) ++ l2).
Proof using.
  introv. gen l2. induction l1; introv Hd S1 S2; rew_list.
  { auto. }
  { rewrite heads_le_cons_l in Hd.
    lets (Hd1&S1'): rsorted_cons_inv (rm S1).
    apply~ IHl1. apply~ sorted_cons. }
Qed.

(** Append of a the reverse of a [sorted] list and a [rsorted] list. *)

Lemma rsorted_app_rev : forall (A : Type) (le : binary A) l1 l2,
  heads_le le l2 l1 ->
  sorted le l1 ->
  rsorted le l2 ->
  rsorted le ((rev l1) ++ l2).
Proof using.
  unfold rsorted. intros. apply~ sorted_app_rev.
  rewrite~ heads_le_flip_eq.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** [rsorts] *)

(** [rsorts le l l'] asserts that [l'] is the result of sorting
    [l] in reverse order w.r.t. [le]. *)

Definition rsorts A (le : binary A) := sorts (flip le).

Section Rsorts.
Variables (A : Type).
Implicit Types le : binary A.
Hint Resolve sorted_nil sorted_one.

Lemma rsorts_refl : forall le l,
  rsorted le l ->
  rsorts le l l.
Proof using. intros. apply~ sorts_refl. Qed.

Lemma rsorts_cons : forall le l l' x,
  rsorts le l l' ->
  head_le (flip le) x l' ->
  rsorts le (x::l) (x::l').
Proof using. intros. applys~ sorts_cons. Qed.

Lemma rsorts_2 : forall le l x1 x2,
  permut l (x1::x2::nil) ->
  le x2 x1 ->
  rsorts le l (x1::x2::nil).
Proof using. intros. applys~ sorts_2. Qed.

Lemma rsorts_3 : forall le l x1 x2 x3,
  permut l (x1::x2::x3::nil) ->
  le x2 x1 ->
  le x3 x2 ->
  rsorts le l (x1::x2::x3::nil).
Proof using. intros. applys~ sorts_3. Qed.

Lemma rsorts_permut : forall l1 l2 l' le,
  rsorts le l1 l' ->
  permut l2 l1 ->
  rsorts le l2 l'.
Proof using. intros. applys* sorts_permut. Qed.

End Rsorts.


(* ---------------------------------------------------------------------- *)
(** ** Building [rsorts] and [sorts] lists as [rev l1 ++ l2]. *)

Section SortsApp.
Variables (A : Type).
Implicit Types le : binary A.

Lemma sorts_app_rev : forall le l1 l2,
  heads_le le l1 l2 ->
  rsorted le l1 ->
  sorted le l2 ->
  sorts le (l1 ++ l2) (rev l1 ++ l2).
Proof using.
  introv H S1 S2. split.
  { apply permut_app_l. apply permut_rev. }
  { apply~ sorted_app_rev. }
Qed.

Lemma rsorts_app_rev : forall le l1 l2,
  heads_le le l2 l1 ->
  sorted le l1 ->
  rsorted le l2 ->
  rsorts le (l1 ++ l2) (rev l1 ++ l2).
Proof using.
  introv H S1 S2. applys* sorts_app_rev. rewrite~ heads_le_flip_eq.
Qed.

End SortsApp.


*)
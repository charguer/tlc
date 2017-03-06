(**************************************************************************
* TLC: A library for Coq                                                  *
* Lists                                                                   *
* See also LibListExec.v and LibListSub.v                                 *
***************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import Coq.Classes.Morphisms. (* for [Proper] instances *)
Require Import LibTactics LibLogic LibReflect LibOperation
 LibProd LibOption LibNat LibInt LibWf LibStruct LibRelation.
Local Open Scope nat_scope.
Local Open Scope comp_scope.
Global Close Scope list_scope.


(* ********************************************************************** *)
(** Fixing implicit arguments *)

Implicit Arguments nil [[A]].
Implicit Arguments cons [[A]].

Inductive create_liblist_scope.
Notation "'create_liblist_scope'" := create_liblist_scope : liblist_scope.

Open Scope liblist_scope.
Delimit Scope liblist_scope with list.
Bind Scope liblist_scope with list.

Infix "::" := cons (at level 60, right associativity) : liblist_scope.

(* Not loaded by default 
Notation "[ ]" := nil (format "[ ]") : liblist_scope. 
Notation "[ x ]" := (cons x nil) : liblist_scope.
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)) : liblist_scope.
*)


(* ********************************************************************** *)
(** * Inhabited *)

Instance list_inhab : forall A, Inhab (list A).
Proof using. intros. apply (prove_Inhab nil). Qed.



(* ********************************************************************** *)
(** * Normalization tactics *)

(* ---------------------------------------------------------------------- *)
(** ** [rew_list] for basic list properties *)

(** Normalize 
  - [++]
  - [length] 
  - [rev]
*)

Tactic Notation "rew_list" :=
  autorewrite with rew_list.
Tactic Notation "rew_list" "~" :=
  rew_list; auto_tilde.
Tactic Notation "rew_list" "*" :=
  rew_list; auto_star.
Tactic Notation "rew_list" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_list).
  (* autorewrite with rew_list in *. *)
Tactic Notation "rew_list" "~" "in" "*" :=
  rew_list in *; auto_tilde.
Tactic Notation "rew_list" "*" "in" "*" :=
  rew_list in *; auto_star.
Tactic Notation "rew_list" "in" hyp(H) :=
  autorewrite with rew_list in H.
Tactic Notation "rew_list" "~" "in" hyp(H) :=
  rew_list in H; auto_tilde.
Tactic Notation "rew_list" "*" "in" hyp(H) :=
  rew_list in H; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** [rew_listx] for more advanced properties 
  -- different from [rew_list] for efficiency reasons *)

(** Normalize 
  - what [rew_list] does
  - [fold_left] except on [++]
  - [fold_right] except on [++]
  - [map]
  - [concat]
  - [split]
  - [combine]
*)

Tactic Notation "rew_listx" :=
  autorewrite with rew_listx.
Tactic Notation "rew_listx" "~" :=
  rew_listx; auto_tilde.
Tactic Notation "rew_list" "*" :=
  rew_listx; auto_star.
Tactic Notation "rew_listx" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_listx).
  (* autorewrite with rew_list in *. *)
Tactic Notation "rew_listx" "~" "in" "*" :=
  rew_listx in *; auto_tilde.
Tactic Notation "rew_listx" "*" "in" "*" :=
  rew_listx in *; auto_star.
Tactic Notation "rew_listx" "in" hyp(H) :=
  autorewrite with rew_listx in H.
Tactic Notation "rew_listx" "~" "in" hyp(H) :=
  rew_listx in H; auto_tilde.
Tactic Notation "rew_listx" "*" "in" hyp(H) :=
  rew_listx in H; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** [rew_lists] for set and map operations on lists *)

(** Normalize 
  - [++]
  - [mem] 
  - [keys]
  - [assoc]
*)

Tactic Notation "rew_lists" :=
  autorewrite with rew_lists.
Tactic Notation "rew_lists" "~" :=
  rew_lists; auto_tilde.
Tactic Notation "rew_lists" "*" :=
  rew_lists; auto_star.
Tactic Notation "rew_lists" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_lists).
  (* autorewrite with rew_lists in *. *)
Tactic Notation "rew_lists" "~" "in" "*" :=
  rew_lists in *; auto_tilde.
Tactic Notation "rew_lists" "*" "in" "*" :=
  rew_lists in *; auto_star.
Tactic Notation "rew_lists" "in" hyp(H) :=
  autorewrite with rew_lists in H.
Tactic Notation "rew_lists" "~" "in" hyp(H) :=
  rew_lists in H; auto_tilde.
Tactic Notation "rew_lists" "*" "in" hyp(H) :=
  rew_lists in H; auto_star.


(* ********************************************************************** *)
(** * Properties of operations *)

(* ---------------------------------------------------------------------- *)
(** ** Core operations *)

Fixpoint fold_right A B (f : A -> B -> B) (acc : B) l :=
  match l with
  | nil => acc
  | x::L' => f x (fold_right f acc L')
  end.

Definition append A (l1 l2 : list A) :=
  fold_right (fun x (acc:list A) => x::acc) l2 l1.

(* Properties appear further *)


(* ---------------------------------------------------------------------- *)
(** ** Notation *)

(** [l1 ++ l2] concatenates two lists *)

Infix "++" := append (right associativity, at level 60) : liblist_scope.

(** [l & x] extends the list [l] with the value [x] at the right end *)

Notation "l & x" := (l ++ (x::nil))
  (at level 28, left associativity) : liblist_scope.


(* ---------------------------------------------------------------------- *)
(** ** App *)

Section App.
Variables A B : Type.
Implicit Types x : A.
Implicit Types l : list A.

Lemma app_cons_l : forall x l1 l2,
  (x::l1) ++ l2 = x :: (l1++l2).
Proof using. auto. Qed.

Lemma app_nil_l : forall l,
  nil ++ l = l.
Proof using. auto. Qed.

Lemma app_nil_r : forall l,
  l ++ nil = l.
Proof using. induction l. auto. rewrite app_cons_l. fequals~. Qed.

Lemma app_assoc : forall l1 l2 l3,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof using.
  intros. induction l1.
  { rewrite_all~ app_nil_l. }
  { rewrite_all~ app_cons_l. fequals~. }
Qed.

Lemma app_cons_r : forall x l1 l2,
  l1 ++ (x::l2) = (l1 & x) ++ l2.
Proof using. intros. rewrite~ app_assoc. Qed.

Lemma app_cons_one : forall x l,
  (x::nil) ++ l = x::l.
Proof using. auto. Qed.

Lemma app_last_l : forall x l1 l2,
  (l1 & x) ++ l2 = l1 ++ (x::l2).
Proof using. intros. rewrite~ <- app_cons_r. Qed.

End App.

Opaque append.

Hint Rewrite app_cons_l app_nil_l app_nil_r app_assoc
  app_cons_one : rew_list.
(* Note: [app_last_l] may be safely added to [rew_list] *)

Hint Rewrite app_cons_l app_nil_l app_nil_r app_assoc
  app_cons_one : rew_listx.

Hint Rewrite app_cons_l app_nil_l app_nil_r app_assoc
  app_cons_one : rew_lists.


(* ---------------------------------------------------------------------- *)
(** * Inversion lemmas for structural composition *)

Section AppInversion.
Variables A : Type.
Implicit Types x : A.
Implicit Types l : list A.

(**------- Cons -------- *)

Lemma cons_case : forall l,
  l = nil \/ exists x l', l = x :: l'.
Proof using.
  intros. destruct l. left*. right*.
Qed.

Lemma cons_eq_nil_inv : forall x l,
  x::l = nil ->
  False.
Proof using. auto_false. Qed.

(* symmetric of previous lemma *)
Lemma nil_eq_cons_inv : forall x l,
  nil = x::l ->
  False.
Proof using. auto_false. Qed.

Lemma list_neq_nil_inv_cons : forall l,
  l <> nil -> 
  exists x q, l = x :: q.
Proof using. introv N. destruct* (@last_case l). Qed.

Lemma cons_eq_cons_inv : forall x1 x2 l1 l2,
  x1 :: l1 = x2 :: l2 -> 
  x1 = x2 :: l1 = l2.
Proof using. introv H. inverts* H. Qed.

(**------- App -------- *)

Lemma app_not_empty_l : forall l1 l2,
  l1 <> nil -> 
  l1 ++ l2 <> nil.
Proof using. introv NE K. apply NE. destruct~ (app_eq_nil_inv _ _ K). Qed.

Lemma app_not_empty_r : forall l1 l2,
  l2 <> nil -> 
  l1 ++ l2 <> nil.
Proof using. introv NE K. apply NE. destruct~ (app_eq_nil_inv _ _ K). Qed.

Lemma app_cancel_l : forall l1 l2 l3,
  l1 ++ l2 = l1 ++ l3 -> 
  l2 = l3.
Proof using.
  introv E. induction l1; rew_list in *. auto. inverts* E.
Qed.

Lemma app_cancel_r : forall l1 l2 l3,
  l1 ++ l3 = l2 ++ l3 -> 
  l1 = l2.
Proof using.
  introv E. lets H: (f_equal (@rev A) E). rew_list in H.
  lets N: app_cancel_l H. applys~ rev_inj. 
Qed.

Lemma app_eq_nil_inv : forall l1 l2,
  l1 ++ l2 = nil -> 
  l1 = nil /\ l2 = nil.
Proof using. destruct l1; destruct l2; intros; tryfalse~; auto. Qed.

(* symmetric of previous lemma *)
Lemma nil_eq_app_inv : forall l1 l2,
  nil = l1 ++ l2 ->
  l1 = nil /\ l2 = nil.
Proof using. intros. symmetry in H. apply* app_eq_nil_inv. Qed.

Lemma app_eq_self_inv_r : forall l1 l2,
  l2 = l1 ++ l2 -> 
  l1 = nil.
Proof using.
  introv E. apply length_zero_inv.
  lets: (func_eq_1 (@length A) E). rew_length in H. math.
Qed.

Lemma app_eq_self_inv_l : forall l1 l2,
  l1 = l1 ++ l2 -> 
  l2 = nil.
Proof using.
  introv E. apply length_zero_inv.
  lets: (func_eq_1 (@length A) E). rew_length in H. math.
Qed.

(**------- Last -------- *)

Lemma last_case : forall l,
  l = nil \/ exists x l', l = l' & x.
Proof using.
  intros. destruct l. left*. right.
  forwards* (x&l'&H): (last_inv_pos_length (a::l)).
    rew_length. math.
Qed.

Lemma last_eq_nil_inv : forall a l,
  l & a = nil -> 
  False.
Proof using. induction l; rew_app; intros; false. Qed.

(* symmetric of previous lemma *)
Lemma nil_eq_last_inv : forall a l,
  nil = l & a -> 
  False.
Proof using. intros. apply* last_eq_nil_inv. Qed.

Lemma list_neq_nil_inv_last : forall l,
  l <> nil -> 
  exists x q, l = q & x.
Proof using. introv N. destruct* (@last_case l). Qed.

Lemma last_eq_last_inv : forall x1 x2 l1 l2,
  l1 & x1 = l2 & x2 -> 
  l1 = l2 /\ x1 = x2.
Proof using.
  introv H. gen l2. induction l1; introv E; rew_app in E.
  destruct l2; rew_app in E; inverts E as E.
   auto. false nil_eq_last_inv E.
  destruct l2; rew_app in E.
    inverts E as E. false last_eq_nil_inv E.
    inverts E. forwards* [? ?]: IHl1.
     split; congruence. (* TODO: congruence that does split *)
Qed.

(**------- Middle -------- *)

Lemma nil_eq_middle_inv : forall x l1 l2,
  nil = l1 & x ++ l2 ->
  False.
Proof using. intros. destruct l1; inverts H. Qed.

Lemma cons_eq_middle_inv : forall x y l1 l2 l,
  x :: l = l1 & y ++ l2 ->
  (l1 = nil /\ x = y /\ l = l2) \/ (exists l1', l1 = x::l1').
Proof using.
  intros. destruct l1; rew_list in H; inverts H.
   left~. right*.
Qed.

End AppInversion.

Implicit Arguments last_eq_nil_inv [A a l].
Implicit Arguments nil_eq_last_inv [A a l].
Implicit Arguments rev_eq_nil_inv [A l].
Implicit Arguments nil_eq_rev_inv [A l].
Implicit Arguments app_eq_nil_inv [A l1 l2].
Implicit Arguments nil_eq_app_inv [A l1 l2].
Implicit Arguments app_rev_eq_nil_inv [A l1 l2].
Implicit Arguments nil_eq_app_rev_inv [A l1 l2].
Implicit Arguments nil_eq_middle_inv [A x l1 l2].
Implicit Arguments cons_eq_middle_inv [A x y l1 l2 l].


(* ---------------------------------------------------------------------- *)
(** ** FoldRight *)

Section FoldRight.
Variables A B : Type.
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types (f : A -> B -> B) (i : B).

Lemma fold_right_nil : forall f i,
  fold_right f i nil = i.
Proof using. auto. Qed.

Lemma fold_right_cons : forall f i x l,
  fold_right f i (x::l) = f x (fold_right f i l) .
Proof using. auto. Qed.

Lemma fold_right_app : forall f i l1 l2,
  fold_right f i (l1 ++ l2) = fold_right f (fold_right f i l2) l1.
Proof using.
  intros. induction~ l1. 
  { rew_list. do 2 rewrite fold_right_cons. fequals~. }
Qed.

Lemma fold_right_last : forall f i x l,
  fold_right f i (l & x) = fold_right f (f x i) l.
Proof using. intros. rewrite~ fold_right_app. Qed.

End FoldRight.

Opaque fold_right.

Hint Rewrite fold_right_nil fold_right_cons fold_right_last : rew_listx.
(* Note: [fold_right_app] may be safely added to [rew_listx] *)


(* ---------------------------------------------------------------------- *)
(** ** FoldLeft *)

Section FoldLeft.
Variables A B : Type.
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types (f : A -> B -> B) (i : B).

Fixpoint fold_left f i l :=
  match l with
  | nil => i
  | x::L' => fold_left f (f x i) L'
  end.

Lemma fold_left_nil : forall f i,
  fold_left f i nil = i.
Proof using. auto. Qed.

Lemma fold_left_cons : forall f i x l,
  fold_left f i (x::l) = fold_left f (f x i) l.
Proof using. auto. Qed.

Lemma fold_left_app : forall f i l1 l2,
  fold_left f i (l1 ++ l2) = fold_left f (fold_left f i l1) l2.
Proof using.
  intros. gen i. induction~ l1.
  { intros. rew_list. do 2 rewrite fold_left_cons. rewrite~ IHl1. }
Qed.

Lemma fold_left_last : forall f i x l,
  fold_left f i (l & x) = f x (fold_left f i l).
Proof using. intros. rewrite~ fold_left_app. Qed.

End FoldLeft.

Opaque fold_left.

Hint Rewrite fold_left_nil fold_left_cons 
  fold_left_last : rew_listx.
(* Note: [fold_left_app] can be safely added to [rew_listx] *)


(* ---------------------------------------------------------------------- *)
(** ** Length *)

Section Length.
Variable A : Type.
Implicit Types l : list A.

Definition length l :=
  fold_right (fun x acc => 1+acc) 0 l.

Lemma length_nil :
  length (@nil A) = 0.
Proof using. auto. Qed.

Lemma length_cons : forall x l,
  length (x::l) = 1 + length l.
Proof using. auto. Qed.

Lemma length_app : forall l1 l2,
  length (l1 ++ l2) = length l1 + length l2.
Proof using.
  intros. unfold length at 1. rewrite fold_right_app.
  fold (length l2). induction l1; rew_listx.
  { auto. }
  { rewrite length_cons. rewrite IHl1. math. }
Qed.

Lemma length_last : forall x l,
  length (l & x) = 1 + length l.
Proof using.
  intros. rewrite length_app, length_cons, length_nil.
  simpl. math.
Qed.

End Length.

Opaque length.

Hint Rewrite length_nil length_cons length_app 
  length_last : rew_list.
Hint Rewrite length_nil length_cons length_app 
  length_last : rew_listx.


(* ---------------------------------------------------------------------- *)
(** ** Inversion for length *)

Section LengthInversion.
Variable A : Type.
Implicit Types l : list A.

Lemma length_zero_inv : forall l,
  length l = 0%nat ->
  l = nil.
Proof using.
  destruct l. auto. rewrite length_cons. intros. false.
Qed.

Lemma length_zero_iff_nil : forall l,
  length l = 0 <-> l = nil.
Proof using.
  intros. iff M. destruct l; simpls; auto_false*. subst*. Qed.

Lemma length_neq_inv : forall l1 l2,
  length l1 <> length l2 -> 
  (l1 <> l2).
Proof using. introv N E. subst. auto. Qed.

Lemma length_pos_inv_cons : forall l, 
  (length l > 0%nat) ->
  exists x l', l = x :: l'.
Proof using.
  introv E. destruct l; rew_list in *.
  { false. math. }
  { eauto. }
Qed.

Lemma length_pos_inv_last : forall l, 
  (length l > 0%nat) ->
  exists x l', l = l' & x.
Proof using.
  induction l; rew_length; introv H.
  false. math.
  destruct l.
    exists~ a (@nil A).
    destruct IHl as (x&l'&E). rew_list in *. math.
    exists x (a::l'). rewrite~ E.
Qed.

End LengthInversion.


(* ---------------------------------------------------------------------- *)
(* ** Mem *)

(** [mem x l] asserts that [x] belongs to [l] *)

Inductive mem A (x:A) : list A -> Prop :=
  | mem_here : forall l,
      memb x (x::l)
  | mem_next : forall y l,
      mem x l ->
      mem x (y::l).

Section Mem.
Variables (A : Type).
Implicit Types x : A.
Implicit Types l : list A.

Hint Constructors mem.

(** Induction *)

Lemma mem_induct : forall (x : A) (P : list A -> Prop),
  (forall l : list A, P (x :: l)) ->
  (forall (y : A) (l : list A), mem x l -> x <> y -> P l -> P (y :: l)) ->
  (forall l : list A, mem x l -> P l).
Proof using.
  introv HH HN M. induction l.
  inverts M.
  tests: (x = a). auto. inverts M; auto_false*.
Qed.

(** Rewriting *)

Lemma mem_nil_eq : forall x,
  mem x nil = False.
Proof using. intros. extens. iff H; inverts H. Qed.

Lemma mem_cons_eq : forall x y l,
  mem x (y::l) = ((x = y) \/ (mem x l)).
Proof using. intros. extens. iff H; inverts~ H. Qed.

Lemma mem_app_or_eq : forall l1 l2 x,
  mem x (l1 ++ l2) = (mem x l1 \/ mem x l2).
Proof using.
  intros. extens. induction l1; rew_app.
  split. auto. introv [H|?]. inverts H. auto.
  iff M. inverts~ M. rewrite IHl1 in H0. destruct* H0.
   destruct M. inverts~ H. constructors. rewrite~ IHl1.
   constructors. rewrite~ IHl1.
Qed.

Lemma mem_last_eq : forall x y l,
  mem x (l&l) = ((mem x l) \/ (x = y)).
Proof using. intros. rewrite mem_app_or_eq. rewrite~ mem_cons_eq. Qed.

(** Backward *)

Lemma mem_cons : forall l x,
  mem x (x::l).
Proof using. intros. apply* mem_here. Qed.

Lemma mem_app : forall l1 l2 x,
  mem x l1 \/ mem x l2 -> 
  mem x (l1 ++ l2).
Proof using. intros. rewrite~ mem_app_or_eq. Qed.

Lemma mem_app_l : forall l1 l2 x,
  mem x l1 -> 
  mem x (l1 ++ l2).
Proof using. intros. applys* mem_app. Qed.

Lemma mem_app_r : forall l1 l2 x,
  mem x l2 -> 
  mem x (l1 ++ l2).
Proof using. intros. applys* mem_app. Qed.

Lemma mem_last : forall l x,
  mem x (l & x).
Proof using. intros. apply* mem_app_or. Qed.

(** Inversion *)

Lemma mem_nil_inv : forall x,
  mem x nil ->
  False.
Proof using. introv E. inverts E. Qed.

Lemma mem_cons_inv : forall l x y,
  mem x (y::l) ->
  x = y \/ (x <> y /\ mem x l).
Proof using. introv E. rewrite~ mem_cons_eq in E. Qed.

Lemma mem_app_inv : forall l x y,
  mem x (l1 ++ l2) ->
  mem x l1 \/ mem x l2.
Proof using. introv E. rewrite~ mem_app_or_eq in E. Qed.

Lemma mem_last_inv : forall l x y,
  mem x (l&y) ->
  (x <> y /\ mem x l) \/ x = y.
Proof using. introv E. rewrite~ mem_last_eq in E. Qed.

Lemma list_no_mem_inv :

Lemma nil_mem : forall l,
  (forall x : A, ~ mem x l) ->
  l = nil.
Proof using. introv P. destruct~ l. false P. simpl. rew_refl*. Qed.

End Mem.

Hint Rewrite mem_nil_eq mem_cons_eq mem_app_or_eq mem_last_eq : rew_listx.


(* ---------------------------------------------------------------------- *)
(* ** Nth as a relation *)

(** [Nth n L x] asserts that the n-th element of the list [L]
    exists and is exactly [x] *)

Inductive Nth A : nat -> list A -> A -> Prop :=
  | Nth_here : forall l x,
      Nth 0 (x::l) x
  | Nth_next : forall y n l x,
      Nth n l x ->
      Nth (S n) (y::l) x.

Section Nth.
Variables (A : Type) (IA : Inhab A).
Implicit Types l : list A.
Implicit Types x : A.
Implicit Types n : nat.
Hint Constructors Nth.

Lemma Nth_func: forall n l x1 x2,
  Nth n l x1 ->
  Nth n l x2 -> 
  x1 = x2.
Proof using. introv H1. induction H1; intro H2; inverts~ H2. Qed.

Lemma Nth_mem : forall l x n,
  Nth n l x -> 
  mem x l.
Proof using. clear IA. introv N. induction N; simpl; rew_refl* in *. Qed.

Lemma mem_Nth : forall l x,
  mem x l -> 
  exists n, Nth n l x.
Proof using.
  intros. induction l.
  rewrite mem_nil in H. false.
  rewrite mem_cons in H. rew_reflect in H. destruct H.
   fold_prop. subst*.
   forwards* [n ?]: IHl.
Qed.

Lemma Nth_inbound : forall n l x,
  Nth n l x -> 
  n < length l.
Proof using.
  induction n; introv H; inverts H.
  rewrite length_cons. math.
  rewrite length_cons. simpl. rew_nat*.
Qed.

Lemma Nth_inbound_inv : forall n l,
  n < length l -> 
  exists x, Nth n l x.
Proof using.
  induction n; introv Comp; destruct l as [|a l'];
    rew_list in Comp; try solve [math].
   eexists. apply Nth_here.
   simpls. rewrite lt_SS in Comp.
    forwards (x&Hx): IHn Comp. exists x.
    apply* Nth_next.
Qed.

Lemma Nth_app_l : forall n x l1 l2,
  Nth n l1 x -> 
  Nth n (l1 ++ l2) x.
Proof using. induction n; introv H; inverts H; rew_list*. Qed.

Lemma Nth_app_r : forall n m x l1 l2,
  Nth m l2 x -> 
  n = (m + length l1)%nat -> 
  Nth n (l1 ++ l2) x.
Proof using.
  intros. subst. gen m. induction l1; introv H.
  rew_list. applys_eq~ H 3.
  rew_list. applys_eq* Nth_next 3.
Qed.

Lemma Nth_nil_inv : forall n x,
  Nth n nil x -> 
  False.
Proof using. introv H. inverts H. Qed.

Lemma Nth_inv_neq_nil : forall n x,
  Nth n l x -> 
  l <> nil.
Proof using. introv H. inverts H. Qed.

Lemma Nth_cons_inv : forall n x l,
  Nth n (y::q) x ->
     (n = 0 /\ x = y )
  \/ (exists m, n = m+1 /\ Nth m q x).
Proof using.
  introv H. inverts H. { left*. } { right. splits~. math. }
Qed.

Lemma Nth_app_inv : forall n x l1 l2,
  Nth n (l1++l2) x ->
     (Nth n l1 x)
  \/ (exists m, n = length l1 + m /\ Nth m l2 x).
Proof using.
  introv. gen n. induction l1; introv H; rew_list in H.
  right. rew_length. exists~ n.
  inverts H. left~.
   forwards* M: IHl1. destruct M.
    left~. unpack. rew_length.
    right*. exists m. split~. math.
Qed.

Lemma Nth_last_inv : forall n x y l,
  Nth n (l&y) x ->
     (Nth n l x)
  \/ (n = length l /\ y = x).
Proof using.
  introv H. destruct [|(?&?&?)]: Nth_app_inv H; eauto.
Qed.

End Nth.


(* ---------------------------------------------------------------------- *)
(** ** Nth as a partial function *)

(*--- [nth] with a default ---*)

Section NthDef.
Variables (A:Type).
Implicit Types n : nat.
Implicit Types d x : A.
Implicit Types l : list A.

Fixpoint nth_def d n l : A :=
  match l with
  | nil => d
  | x::l' =>
     match n with
     | 0 => x
     | S n' => nth_def d n' l'
     end
  end.

Lemma nth_def_nil : forall n d,
  nth_def d n nil = d.
Proof using. introv. destruct~ n. Qed.

Lemma nth_def_zero : forall x l d,
  nth_def d 0 (x::l) = x.
Proof using. introv. reflexivity. Qed.

Lemma nth_def_succ : forall n x l d,
  nth_def d (S n) (x::l) = nth_def d n l.
Proof using. introv. reflexivity. Qed.

Definition nth_def_cons := nth_def_succ.

End NthDef.

Arguments nth_def [A] : simpl never.

Hint Rewrite nth_def_nil nth_def_zero nth_def_succ : rew_listx.

(*--- [nth] with an arbitrary default ---*)

Section NthFunc.
Context (A:Type) {IA: Inhab A}.
Implicit Types n : nat.
Implicit Types x : A.
Implicit Types l : list A.

Definition nth := nth_def arbitrary.

Lemma nth_zero : forall x l,
  nth 0 (x::l) = x.
Proof using. intros. apply nth_def_zero. Qed.

Lemma nth_succ : forall n x l,
  nth (S n) (x::l) = nth n l.
Proof using. intros. apply nth_def_succ. Qed.

Definition nth_cons := nth_succ.

Lemma nth_pos : forall n x l,
  n > 0 ->
  nth n (x::l) = nth (n-1) l.
Proof using.
  intros. destruct n. 
  { false. math. } 
  { rewrite nth_succ. fequals. math. } 
Qed.

End NthFunc.

Arguments nth [A] {IA}.
Opaque nth.

Hint Rewrite nth_zero nth_succ : rew_listx.



Lemma mem_nth : forall l x,
  mem x l -> 
  exists n, nth n l = x.
Proof using.
  intros. forwards [n P]: mem_Nth H.
  exists n. apply~ Nth_to_nth.
Qed.


Lemma Nth_to_nth_def : forall n l x dummy,
  Nth n l x -> nth_def dummy n l = x.
Proof using. introv H. induction~ H. Qed.

Lemma Nth_to_nth : forall n l x,
  Nth n l x -> nth n l = x.
Proof using. introv H. apply~ Nth_to_nth_def. Qed.





Lemma nth_def_if_in_length : forall l d n v,
  n < length l ->
  nth_def d n l = v ->
  Nth n l v.
Proof using.
  introv I E. forwards (v'&Nv): length_Nth_lt I.
  erewrite Nth_to_nth_def in E; [| apply~ Nv ]. substs~.
Qed.

Lemma Forall2_Nth_nth_def : forall A B (P : A -> B -> Prop) la lb n v d,
  Forall2 P la lb ->
  Nth n la v ->
  Nth n lb (nth_def d n lb).
Proof using.
  introv F N. forwards L: Forall2_length F. forwards I: Nth_lt_length N.
  rewrite L in I. forwards*: nth_def_if_in_length I.
Qed.




(* ---------------------------------------------------------------------- *)
(** ** Rev *)

Section Rev.
Variable A : Type.
Implicit Types x : A.
Implicit Types l : list A.

Definition rev l :=
  fold_left (fun x acc => x::acc) (@nil A) l.

Lemma rev_nil :
  rev (@nil A) = nil.
Proof using. auto. Qed.

Lemma rev_app : forall l1 l2,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof using.
  intros. unfold rev. asserts K1: (forall l accu,
   fold_left (fun x acc => x :: acc) accu l =
   fold_left (fun x acc => x :: acc) nil l ++ accu).
  { induction l; intros.
    { auto. }
    { rew_listx. rewrite IHl. rewrite (@IHl (a::nil)). rew_list~. } }
  asserts K2: (forall accu,
   fold_left (fun x acc => x :: acc) accu (l1 ++ l2) =
   fold_left (fun x acc => x :: acc) nil l2 ++
   fold_left (fun x acc => x :: acc) nil l1 ++ accu).
  { induction l1; intros.
    { rew_list. apply K1. }
    { rew_listx. rewrite IHl1. rewrite (@K1 l1 (a::nil)). rew_list~. } }
  lets K3: (@K2 nil). rewrite app_nil_r in K3. auto.
Qed.

Lemma rev_cons : forall x l,
  rev (x::l) = rev l & x.
Proof using. intros. rewrite <- app_cons_one. rewrite~ rev_app. Qed.

Lemma rev_last : forall x l,
  rev (l & x) = x::(rev l).
Proof using. intros. rewrite~ rev_app. Qed.

Lemma rev_rev : forall l,
  rev (rev l) = l.
Proof using.
  intros. induction~ l. { rewrite rev_cons, rev_last. fequals. }
Qed.

Lemma rev_inj : forall l1 l2,
  rev l1 = rev l2 ->
  l1 = l2.
Proof using.
   introv E. forwards E': f_equal rev (rm E).
   do 2 rewrite~ rev_rev in E'. 
Qed.

Lemma mem_rev : forall l x,
  mem x l -> 
  mem x (rev l).
Proof using. introv H. induction H; rew_rev; apply~ mem_app_or. Qed.

Lemma mem_rev_iff : forall l x,
  mem x l <-> mem x (rev l).
Proof using.
  iff M.
  { apply~ mem_rev. }
  { lets H: mem_rev M. rewrite~ rev_rev in H. }
Qed.

Lemma length_rev : forall l,
  length (rev l) = length l.
Proof using. intros. induction~ l. { rewrite rev_cons. rew_list~. } Qed.

Lemma fold_right_rev : forall B (f : A -> B -> B) i l,
  fold_right f i (rev l) = fold_left f i l.
Proof using.
  introv. gen i. induction~ l.
  { introv. rewrite rev_cons. rew_listx~. }
Qed.

End Rev.

Opaque rev.

Hint Rewrite rev_nil rev_app rev_cons rev_last rev_rev length_rev : rew_list.
Hint Rewrite rev_nil rev_app rev_cons rev_last rev_rev length_rev : rew_listx.
(* Note: [fold_right_rev] may be safely added to [rew_list] *)


(* ---------------------------------------------------------------------- *)
(** ** Inversion for rev *)

Section RevInversion.
Variable A : Type.
Implicit Types l : list A.

Lemma rev_eq_nil_inv : forall l,
  rev l = nil -> 
  l = nil.
Proof using.
  destruct l; rew_rev; intros. auto.
  false* last_eq_nil_inv.
Qed.

(* symmetric of previous lemma *)
Lemma nil_eq_rev_inv : forall l,
  nil = rev l ->
  l = nil.
Proof using. introv H. apply~ rev_eq_nil_inv. Qed.

Lemma app_rev_eq_nil_inv : forall l1 l2,
  l1 ++ rev l2 = nil -> 
  l1 = nil /\ l2 = nil.
Proof using.
  intros. lets H1 H2: (app_eq_nil_inv _ _ H).
  applys_to H2 rev_eq_nil_inv. autos*.
Qed.

(* symmetric of previous lemma *)
Lemma nil_eq_app_rev_inv : forall l1 l2,
  nil = l1 ++ rev l2 -> 
  l1 = nil /\ l2 = nil.
Proof using. intros. apply* app_rev_eq_nil_inv. Qed.

End RevInversion.



(* ---------------------------------------------------------------------- *)
(* ** No_duplicates *)

(** [No_duplicates L] asserts that [L] does not contain any
    duplicated item. *)

Inductive No_duplicates A : list A -> Prop :=
  | No_duplicates_nil : No_duplicates nil
  | No_duplicates_cons : forall x l,
      ~ (Mem x l) -> No_duplicates l -> No_duplicates (x::l).

Section No_duplicates_Prop.
Variable (A : Type).
Implicit Types l : list A.

Lemma No_duplicates_app : forall l1 l2,
  No_duplicates l1 ->
  No_duplicates l2 ->
  (forall x, mem x l1 -> mem x l2 -> False) ->
  No_duplicates (l1 ++ l2).
Proof using.
  Hint Constructors Mem.
  intros l1. induction l1; introv N1 N2 EQ; rew_list.
  auto.
  inverts N1 as N N1'. constructors.
    rewrite mem_app_or_eq. rew_logic*.
    applys~ IHL1. introv Mx1 Mx2. applys* EQ x.
Qed.

Lemma No_duplicates_app_inv : forall l1 l2,
  No_duplicates (l1 ++ l2) ->
     No_duplicates l1
  /\ No_duplicates l2 
  /\ ~ (exists x, mem x l1 /\ mem x l2).
Proof using.
  introv ND. splits.
   induction l1.
    constructors.
    rew_list in ND. inverts ND as ND1 ND2. rewrite mem_app_or_eq in ND1. rew_logic* in ND1.
   induction l1.
    rew_list~ in ND.
    rew_list in ND. inverts~ ND.
   introv (x&I1&I2). rewrite <- Mem_mem in *. induction I1; rew_list in ND.
    inverts ND as ND1 ND2. false ND1. apply* mem_app_or.
    apply IHI1. inverts~ ND.
Qed.

Lemma No_duplicates_length_le : forall l1 l2,
  No_duplicates l1 ->
  (forall x, mem x l1 -> mem x l2) ->
  (length l1 <= length l2)%nat.
Proof using.
  Hint Constructors Mem.
  introv NL ML. gen L'. induction L as [|a L]; intros.
  rew_length. math.
  rew_length. inverts NL as HM NL'.
   sets_eq L'': (Filter (<> a) L').
   forwards H: Filter_neq_Mem_length a L'. applys* ML.
   rewrite <- EQL'' in H.
   forwards~: IHL L''. introv N. tests: (x = a). subst L''. applys* Filter_Mem.
   math.
Qed.

Lemma No_duplicates_length_eq : forall l1 l2,
  No_duplicates l1 ->
  No_duplicates l2 ->
  (forall x, mem x l1 <-> mem x l2) ->
  (length l1 = length l2)%nat.
Proof using.
  introv HL HL' EQ.
  forwards~: No_duplicates_length_le L L'. intros. rewrite~ <- EQ.
  forwards~: No_duplicates_length_le L' L. intros. rewrite~ EQ.
  math.
Qed.

Lemma No_duplicates_Nth_same  : forall l,
  (forall n1 n2 x,
     Nth n1 l x ->
     Nth n2 l x ->
     n1 = n2) ->
  No_duplicates l.
Proof using.
  introv NL. induction L; constructors.
   introv I. rewrite Mem_mem in I. lets (n&N): mem_Nth (rm I).
    forwards* Ab: NL Nth_here Nth_next. inverts Ab.
   apply IHL. introv N1 N2. forwards G: NL.
    applys Nth_next N1.
    applys Nth_next N2.
    inverts~ G.
Qed.

Lemma No_duplicates_Nth_same_inv : forall l n1 n2 x,
  No_duplicates l ->
  Nth n1 l x ->
  Nth n2 l x ->
  n1 = n2.
Proof using.
  introv NL. gen n1 n2. induction NL; introv N1 N2.
   inverts N1.
   inverts N1 as N1; inverts N2 as N2; autos~.
    apply Nth_mem in N2. rewrite <- Mem_mem in N2. false*.
    apply Nth_mem in N1. rewrite <- Mem_mem in N1. false*.
Qed.

End No_duplicates_Prop.


(* ---------------------------------------------------------------------- *)
(** ** Map *)

Section Map.
Variable (A B : Type).
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types f : A -> B.

Definition map f l :=
  fold_right (fun x acc => (f x)::acc) (@nil B) l.

Lemma map_nil : forall f,
  map f nil = nil.
Proof using. auto. Qed.

Lemma map_cons : forall f x l,
  map f (x::l) = f x :: map f l.
Proof using. auto. Qed.

Lemma map_app : forall f l1 l2,
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof using.
  intros. unfold map.
  assert (forall accu,
    fold_right (fun x acc => f x :: acc) accu (l1 ++ l2) =
    fold_right (fun x acc => f x :: acc) nil l1 ++
     fold_right (fun x acc => f x :: acc) nil l2 ++ accu).
  { induction l1; intros; simpl.
     { rew_list. gen accu.
       induction l2; intros. 
       { auto. }
       { rew_listx. rewrite~ IHl2. } }
     { rew_listx. fequals. } }
  specializes H (@nil B). rew_list~ in H.
Qed.

Lemma map_last : forall f x l,
  map f (l & x) = map f l & f x.
Proof using. intros. rewrite~ map_app. Qed.

Lemma map_rev : forall f l,
  map f (rev l) = rev (map f l).
Proof using.
  intros. induction~ l.
  { rewrite map_cons. rew_list. rewrite map_last. rewrite~ IHl. }
Qed.

Lemma length_map : forall f l,
  length (map f l) = length l.
Proof using.
  intros. induction~ l. 
  { rewrite map_cons. do 2 rewrite length_cons. auto. }
Qed.

Lemma map_eq_nil_inv : forall f l,
  map f l = nil -> 
  l = nil.
Proof using.
  introv E. destruct~ l. rewrite map_cons in E. false.
Qed.

Lemma map_inj : forall f l1 l2,
  (forall x y, f x = f y -> x = y) ->
  map f l1 = map f l2 ->
  l1 = l2.
Proof using.
  intros f l1. induction l1; introv I E.
  { rewrite map_nil in E. forwards*: map_eq_nil_inv. }
  { destruct l2 as [|b l2]; tryfalse. do 2 rewrite map_cons in E.
    inverts E. fequals*. }
Qed.

End Map.

Opaque map.

Hint Rewrite map_nil map_cons map_app map_last : rew_listx.
(* Note: [map_rev] and [map_id] may be safely added to [rew_listx] *)

Lemma map_id : forall A (l:list A),
  map id l = l.
Proof using. introv. induction~ l. rew_listx. fequals~. Qed.

Lemma mem_map : forall (A B:Type) (f:A->B) (l: list A) x,
  mem x l -> 
  mem (f x) (map f l).
Proof using. introv M. induction M; rew_listx; auto. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Concat *)

Section Concat.
Variable A : Type.
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types m : list (list A).

Definition concat m :=
  fold_right (@append A) (@nil A) m.

Lemma concat_nil :
  concat (@nil (list A)) = nil.
Proof using. auto. Qed.

Lemma concat_cons : forall l m,
  concat (l::m) = l ++ concat m.
Proof using. auto. Qed.

Lemma concat_one : forall l,
  concat (l::nil) = l.
Proof using.
  intros. rewrite concat_cons. rewrite concat_nil. rew_list~.
Qed.

Lemma concat_app : forall m1 m2 : list (list A),
  concat (m1 ++ m2) = concat m1 ++ concat m2.
Proof using.
  intros m1. induction m1; intros.
  { rewrite concat_nil. rew_list~. }
  { rew_list. do 2 rewrite concat_cons. rew_list. fequals. }
Qed.

Lemma concat_last : forall l m,
  concat (m & l) = concat m ++ l.
Proof using. intros. rewrite~ concat_app. rewrite~ concat_one. Qed.

(* TODO: length_concat *)

Lemma mem_concat_iff : forall m x,
      mem x (concat m)
  <-> exists l, mem l m /\ mem x l.
Proof using.
  introv. induction Ls.
   simpl. iff I; inverts* I.
  rewrite concat_cons. iff I.
   rewrite mem_app in I. rew_refl in *. inverts I as I.
    exists a. splits~. rewrite mem_cons. rew_refl*.
    apply IHLs in I. lets (l&Il&Ix): (rm I).
     exists l. rewrite mem_cons. rew_refl*.
   rewrite mem_app. rew_refl. lets (l&Il&Ix): (rm I).
    rewrite mem_cons in Il. rew_refl in Il. inverts Il as Il.
     left~.
     right~. apply* IHLs.
Qed.

Lemma concat_eq_nil_mem_inv : forall l m,
  concat m = nil ->
  mem l m ->
  l = nil.
Proof using.
  intros m. induction m; introv E I; inverts I as I.
  rewrite concat_cons in E. fold_bool. rew_refl in I.
  forwards (?&C): app_eq_nil_inv (rm E). substs. inverts~ I.
Qed.

End Concat.

Opaque concat.

Hint Rewrite concat_nil concat_app concat_cons concat_last : rew_listx.


(* ---------------------------------------------------------------------- *)
(** ** Filter *)

Section Filter.
Variable (A : Type).
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types P : A -> Prop.


  Definition filter f l :=
    fold_right (fun x acc => if f x then x::acc else acc) (@nil A) l.

  Lemma filter_nil : forall f,
    filter f nil = nil.
  Proof using. auto. Qed.

  Lemma filter_cons : forall f x l,
    filter f (x::l) = if f x then x :: filter f l else filter f l.
  Proof using. auto. Qed.

  Lemma filter_app : forall f l1 l2,
    filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
  Proof using.  
    (* LATER: investigate how to factorise with proof of map_app *)
    intros. unfold filter.
    assert (forall accu,
      fold_right (fun x acc => if f x then x::acc else acc) accu (l1 ++ l2) =
      fold_right (fun x acc => if f x then x::acc else acc) nil l1 ++
       fold_right (fun x acc => if f x then x::acc else acc) nil l2 ++ accu).
    { induction l1; intros; simpl. 
      do 2 rewrite app_nil_l. gen accu.
      induction l2; intros.
      { auto. }
      { do 2 rewrite fold_right_cons. 
        case_if. rew_list. fequals. rewrite IHl2. fequals. }
      { rew_listx. case_if. rew_list. fequals. rewrite IHl1. fequals. } }
    specializes H (@nil A). rewrite~ app_nil_r in H.
  Qed.

  Lemma filter_last : forall f x l,
    filter f (l & x) = filter f l ++ (if f x then x::nil else nil).
  Proof using. intros. rewrite~ filter_app. Qed.

  (* TODO: add length_filter *)


End Filter.

Opaque filter.    



Section Filter.
Variables (A : Type).
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types P : A -> Prop.


Lemma Forall_filter_same : forall (f : A -> bool) l,
  Forall f (filter f l).
Proof using.
  introv. induction l.
   rewrite filter_nil. constructors~.
   rewrite filter_cons. cases_if~.
Qed.

(** [filter P L] produces a list [L'] that is the sublist of [L]
    made exactly of the elements of [L] that satisfy [P]. *)

Definition filter P l :=
  fold_right (fun x acc => If P x then x::acc else acc) (@nil A) l.

Lemma filter : forall P,
  filter P nil = nil.
Proof using. auto. Qed.

Lemma filter_cons : forall x l P,
  filter P (x::l) = If P x then x :: filter P l else filter P l.
Proof using. auto. Qed.

Lemma filter_app : forall l1 l2 P,
  filter P (l1 ++ l2) = filter P l1 ++ filter P l2.
Proof using.  (* todo: factorise with map_app and above *)
  intros. unfold filter.
  assert (forall accu,
    fold_right (fun x acc => If P x then x::acc else acc) accu (l1 ++ l2) =
    fold_right (fun x acc => If P x then x::acc else acc) nil l1 ++
     fold_right (fun x acc => If P x then x::acc else acc) nil l2 ++ accu).
  induction l1; intros; simpl.
   do 2 rewrite app_nil_l. gen accu.
   induction l2; intros; simpl.
     auto.
     case_if. fequals. rewrite IHl2. rewrite~ app_cons. fequals.
     case_if. fequals. rewrite IHl1. rewrite~ app_cons. apply IHl1.
  specializes H (@nil A). rewrite~ app_nil_r in H.
Qed.

Lemma filter_last : forall x l P,
  filter P (l & x) = filter P l ++ (If P x then x::nil else nil).
Proof using. intros. rewrite~ filter_app. Qed.

Lemma filter_neq : forall x (L:list A),
  ~ Mem x (filter (<> x) L).
Proof using.
  intros. induction L.
  rewrite filter_nil. introv M. inverts M.
  rewrite filter_cons. case_if.
    introv M. inverts M; false.
    auto.
Qed.

Lemma filter_Mem : forall x (L:list A) (P:A->Prop),
  Mem x L -> P x -> Mem x (filter P L).
Proof using.
  Hint Constructors Mem.
  introv H Px. induction H using Mem_induct.
  rewrite filter_cons. case_if*.
  rewrite filter_cons. case_if*.
Qed.

Lemma filter_Mem_inv : forall x (L:list A) P,
  Mem x (filter P L) -> Mem x L /\ P x.
Proof using.
  Hint Constructors Mem.
  introv M. induction L.
  rewrite filter_nil in M. inverts M.
  rewrite filter_cons in M. case_if. inverts* M. autos*.
Qed.

Lemma filter_length_le : forall (L:list A) P,
  (length (filter P L) <= length L)%nat.
Proof using.
  intros. induction L.
  rewrite filter_nil. math.
  rewrite filter_cons. case_if; rew_length; math.
Qed.

Lemma filter_eq_Mem_length : forall x (L:list A),
  Mem x L -> (length (filter (= x) L) >= 1)%nat.
Proof using.
  introv M. induction L.
  inverts M.
  rewrite filter_cons. case_if.
    rew_list. nat_math.
    inverts M. false. applys~ IHL.
Qed.

Lemma filter_neq_Mem_length : forall x (L:list A),
  Mem x L -> (length (filter (<> x) L) < length L)%nat.
Proof using.
  introv M. induction L.
  inverts M.
  rewrite filter_cons. case_if.
    inverts M. false. rew_length. forwards~: IHL. math.
    lets: (filter_length_le L (<> x)). rew_length. math.
Qed.

Lemma filter_disjoint_predicates_length : forall (P Q:A-> Prop) L,
  (forall x, Mem x L -> P x -> Q x -> False) ->
  (length (filter P L) + length (filter Q L) <= length L)%nat.
Proof using.
  introv. induction L; introv H.
  rew_list. nat_math.
  specializes IHL. intros. applys* H x.
  repeat rewrite filter_cons. do 2 case_if; rew_list.
    false* H.
    nat_math.
    nat_math.
    nat_math.
Qed.

Lemma filter_negated_predicates_length : forall (P:A-> Prop) L,
  length (filter (fun x => P x) L) + length (filter (fun x => ~ P x) L) <= length L.
Proof using.
  intros. applys~ filter_disjoint_predicates_length P (fun x => ~ P x) L.
Qed.

Lemma filter_No_duplicates : forall (L:list A) p,
  No_duplicates L -> No_duplicates (filter p L).
Proof using.
  Hint Constructors No_duplicates.
  introv H. induction H.
  rewrite* filter_nil.
  rewrite filter_cons. case_if.
    constructors*. introv N. rewrite Mem_mem in N. rewrite filter_mem_eq in N.
     rew_refl in N. rewrite* <- Mem_mem in N.
    auto.
Qed.

End Filter.


Lemma No_duplicates_filter : forall l P,
  No_duplicates L -> 
  No_duplicates (filter P L).
Proof using.
  Hint Constructors No_duplicates.
  introv H. induction H.
  rewrite* filter_nil.
  rewrite filter_cons. case_if.
    constructors*. introv N. false* Filter_Mem_inv N.
    auto.
Qed.



(* ---------------------------------------------------------------------- *)
(** ** Forall_bool *)

(* LATER: properties of [forall_bool] *)

Definition forall_bool A (f : A->bool) (l:list A) :=
  fold_right (fun x acc => acc && (f x)) true l.

Opaque forall_bool.


(* ---------------------------------------------------------------------- *)
(** ** Exists_bool *)

(* LATER: properties of [exists_bool] *)

Definition exists_bool A (f : A->bool) (l:list A) :=
  fold_right (fun x acc => acc || (f x)) false l.

Opaque forall_bool.


(* ---------------------------------------------------------------------- *)
(** ** Combine *)

Section Combine.
Variable (A B : Type).
Implicit Types r : list A.
Implicit Types s : list B.

Fixpoint combine r s : list (A*B) :=
  match r with
  | nil => nil
  | a::r' =>
    match s with
    | nil => arbitrary
    | b::s' => (a,b)::(combine r' s')
    end
  end.

Lemma combine_nil : 
  combine (@nil A) (@nil B) = nil.
Proof using. auto. Qed.

Lemma combine_cons : forall x r y s,
  combine (x::r) (y::s) = (x,y)::(combine r s).
Proof using. auto. Qed.

Lemma combine_app : forall r1 r2 s1 s2,
  length r1 = length s1 ->
  combine (r1++r2) (s1++s2) = (combine r1 s1)++(combine r2 s2).
Proof using. 
  intros r1. induction r1; introv E; destruct s1; tryfalse.
  { auto. }
  { rew_list in *. do 2 rewrite combine_cons. rew_list. rewrite~ IHr1. }
Qed.  

Lemma combine_last : forall x r y s,
  length r = length s ->
  combine (r&x) (s&y) = (combine r s)&(x,y).
Proof using. introv E. applys~ combine_app. Qed.

Lemma combine_rev : forall r s,
  length r = length s ->
  combine (rev r) (rev s) = rev (combine r s).
Proof using. 
  intros r. induction r; introv E; destruct s; tryfalse.
  { auto. }
  { rew_list in *. rewrite combine_last, combine_cons.
    { rewrite IHr. rew_list~. math. }
    { rew_list. math. } }
Qed.

Lemma length_combine : forall r s,
  length r = length s ->
  length (combine r s) = length r.
Proof using.
  intros r. induction r; introv E; destruct s; tryfalse.
  { auto. }
  { rewrite combine_cons. rew_list~. }
Qed.

End Combine.

Opaque combine.

Hint Rewrite combine_nil combine_cons : rew_listx.


(* ---------------------------------------------------------------------- *)
(** ** Split *)

Section Split.
Variable (A B : Type).
Implicit Types (l : list (A*B)).

Fixpoint split l : (list A * list B) :=
  match l with
  | nil => (nil,nil)
  | (a,b)::l' => let (la,lb) := split l' in (a::la, b::lb)
  end.

Lemma split_nil : 
  split nil = (nil, nil).
Proof using. auto. Qed.

Lemma split_cons_let : forall x1 x2 l,
  split ((x1,x2)::l) = let '(l1,l2) := split l in (x1::l1, x2::l2).
Proof using. auto. Qed.

Lemma split_cons : forall x1 x2 l s1 s2,
  (s1,s2) = split l ->
  split ((x1,x2)::l) = (x1::s1, x2::s2).
Proof using.
  introv H. rewrite split_cons_let. rewrite~ <- H.
Qed.

Lemma split_app : forall l1 l2 s11 s12 s21 s22,
  (s11,s12) = split l1 ->
  (s21,s22) = split l2 ->
  split (l1++l2) = (s11++s21, s12++s22).
Proof using.
  intros l1. induction l1 as [|[x1 x2] l1']; introv H1 H2.
  { rewrite split_nil in H1. inverts~ H1. }
  { rewrite split_cons_let in H1. destruct (split l1') as [s11' s12'].
    inverts H1. rew_list. rewrite split_cons_let. 
    erewrite~ (IHl1' l2). }
Qed.

Lemma split_last : forall x1 x2 l s1 s2,
  (s1,s2) = split l ->
  split (l&(x1,x2)) = (s1&x1, s2&x2).
Proof using. introv H. erewrite split_app; fequals. Qed.

Lemma split_length_l : forall l s1 s2,
  (s1,s2) = split l ->
  length s1 = length l.
Proof using. 
  intros l. induction l as [|[x1 x2] l']; introv E.
  { rewrite split_nil in E. inverts~ E. } 
  { rewrite split_cons_let in E. destruct (split l') as [s1' s2'].
    inverts E. rew_list. erewrite~ IHl'. }
Qed.

End Split.

Opaque split.

Hint Rewrite split_nil : rew_listx.


(* ---------------------------------------------------------------------- *)
(** ** Take *)

Section Take.
Variable (A : Type).
Implicit Types n : nat.
Implicit Types x : A.
Implicit Types l : list A.

Fixpoint take n l : list A :=
  match n with
  | 0 => nil
  | S n' => match l with
    | nil => nil
    | a::l' => a::(take n' l')
    end
  end.

Lemma take_zero : forall l,
  take 0 l = nil.
Proof using. auto. Qed.

Lemma take_succ : forall x l n,
  take (S n) (x::l) = x :: (take n l).
Proof using. auto. Qed.

Definition take_cons := take_succ.

Lemma take_cons_pos : forall x l n,
  (n > 0) ->
  take n (x::l) = x :: (take (n-1) l).
Proof using.
  introv H. destruct n. false; math.
  rewrite take_cons. fequals_rec. math.
Qed.

Lemma take_app_l : forall n l l',
  (n <= length l) ->
  take n (l ++ l') = take n l.
Proof using.
  induction n; destruct l; introv H; rew_list in *; auto.
  { false. math. }
  { do 2 rewrite take_cons. fequals. applys IHn. math. }
Qed.

Lemma take_app_r : forall n l l',
  (n >= length l) ->
  take n (l ++ l') = l ++ take (n - length l) l'.
Proof using.
  intros. gen n. induction l; introv H.
  { rewrite length_nil in *. do 2 rewrite app_nil_l.
    fequals. math. }
  { rewrite length_cons in *. destruct n as [|n'].
    { false. math. }
    { rew_list. rewrite take_cons. fequals. applys IHl. math. } }
Qed.

Lemma take_prefix_length : forall l l',
  take (length l) (l ++ l') = l.
Proof using.
  intros. rewrite take_app_r; [|math].
  math_rewrite (forall a, a - a = 0).
  rewrite take_zero. rew_list~.
Qed.

Lemma take_full_length : forall l,
  take (length l) l = l.
Proof using.
  intros. lets H: (@take_prefix_length l nil). rew_list~ in H.
Qed.

End Take.

(* Arguments take [A] : simpl never. *)
Opaque take.

Hint Rewrite take_zero take_succ : rew_list.
(* Note: [take_prefix_length] and [take_full_length] 
   may be safely added to [rew_list]. *)


(* ---------------------------------------------------------------------- *)
(** ** Drop *)

Section Drop.
Variable (A : Type).
Implicit Types n : nat.
Implicit Types x : A.
Implicit Types l : list A.

Fixpoint drop n l : list A :=
  match n with
  | 0 => l
  | S n' => match l with
    | nil => nil
    | a::l' => drop n' l'
    end
  end.

Lemma drop_zero : forall l,
  drop 0 l = l.
Proof using. auto. Qed.

Lemma drop_succ : forall x l n,
  drop (S n) (x::l) = (drop n l).
Proof using. auto. Qed.

Definition drop_cons := drop_succ.

Lemma drop_cons_pos : forall x l n,
  (n > 0) ->
  drop n (x::l) = drop (n-1) l.
Proof using.
  introv H. destruct n. false; math.
  rewrite drop_cons. fequals_rec. math.
Qed.

Lemma drop_app_l : forall n l l',
  (n <= length l) ->
  drop n (l ++ l') = drop n l ++ l'.
Proof using.
  induction n; destruct l; introv H; rew_list in *; auto.
  { false. math. }
  { do 2 rewrite drop_cons. fequals. applys IHn. math. }
Qed.

Lemma drop_app_r : forall n l l',
  (n >= length l) ->
  drop n (l ++ l') = drop (n - length l) l'.
Proof using.
  induction n; destruct l; introv H; rew_list in *; auto.
  { false. math. }
  { rewrite drop_cons. rewrite IHn. fequals. math. }
Qed.

Lemma drop_app_length : forall l l',
  drop (length l) (l ++ l') = l'.
Proof using.
  intros. rewrite drop_app_r; [|math].
  math_rewrite (forall a, a - a = 0).
  rewrite drop_zero. rew_list~.
Qed.

Lemma drop_at_length : forall l,
  drop (length l) l = nil.
Proof using.
  intros. lets H: (@drop_app_length l nil). rew_list~ in H.
Qed.

End Drop.

Opaque drop.
(* Arguments drop [A] : simpl never. *)

Hint Rewrite drop_zero drop_succ : rew_list.
(* Note: [drop_prefix_length] and [drop_full_length] 
   may be safely added to [rew_list]. *)


(* ---------------------------------------------------------------------- *)
(** ** Take and Drop decomposition *)

Section TakeAndDrop.
Variable (A : Type).
Implicit Types x : A.
Implicit Types l : list A.

Lemma take_and_drop_struct : forall n l f r,
  f = take n l -> 
  r = drop n l -> 
  n <= length l ->
     l = f ++ r 
  /\ length f = n
  /\ length r = length l - n.
Proof using.
  intros n. induction n; introv F R L.
  { subst. rew_list. splits~. math. }
  { destruct l; rew_list in L.
    { rew_list in L. false. math. }
    { forwards~ (F'&R'&L'): (>> IHn l (take n l) r). { math. }
      subst f. rew_list. splits. { fequals. } { math. } { math. } } }
Qed.

Lemma take_struct : forall n l,
  n <= length l ->
  exists l', length (take n l) = n
          /\ l = (take n l) ++ l'.
Proof using. introv E. forwards* (E1&E2&E3): take_and_drop_struct. Qed.

Lemma length_take : forall n l,
  n <= length l ->
  length (take n l) = n.
Proof using. introv E. forwards~ (l'&N&M): take_struct n l. Qed.

Lemma drop_struct : forall n l,
  n <= length l ->
  exists l', length l' = n 
          /\ l = l' ++ (drop n l).
Proof using. introv E. forwards* (E1&E2&E3): take_and_drop_struct. Qed.

Lemma length_drop : forall n l,
  n <= length l ->
  length (drop n l) = length l - n.
Proof using.
  introv E. forwards~ (l'&N&M): drop_struct n l.
  pattern l at 2. rewrite M. rew_list. math.
Qed.

End TakeAndDrop.

Arguments take_and_drop_struct [A].
Arguments take_struct [A].
Arguments drop_struct [A].


(* ---------------------------------------------------------------------- *)
(** ** TakeDropLast *)

Section TakeDropLast.
Context (A:Type) {IA:Inhab A}.
Implicit Types x : A.
Implicit Types l : list A.

Fixpoint take_drop_last l : (list A)*A :=
  match l with
  | nil => arbitrary
  | x::l' =>
    match l' with
    | nil => (nil,x)
    | _ => let (t,y) := take_drop_last l' in
           (x::t, y)
    end
  end.

Lemma take_drop_last_cons : forall (x:A) (l: list A),
  take_drop_last (x::l) = 
    match l with 
    | nil => (nil, x)
    | _::_ => let (t, y) := take_drop_last l in (x :: t, y)
    end.
Proof using. auto. Qed.

Lemma take_drop_last_spec : forall (x:A) (l l': list A),
  (l',x) = take_drop_last l -> 
  l <> nil ->
  l = l' & x.
Proof using.
  induction l as [|a t]; introv E N. false.
  rewrite take_drop_last_cons in E.
  destruct (take_drop_last t) as [u r].
  { destruct t; inverts E. rewrite* app_nil_l.
    rew_list. fequals. applys IHt; auto_false*. }
Qed.

Lemma take_drop_last_length : forall l l' x,
  (l',x) = take_drop_last l -> 
  l <> nil ->
  length l' = length l - 1.
Proof using.
  introv E N. forwards: take_drop_last_spec E N.
  subst l. rewrite length_last. math.
Qed.

End TakeDropLast.

Opaque take_drop_last.
Arguments take_drop_last [A] {IA}.
Arguments take_drop_last_spec [A] {IA}.
Arguments take_drop_last_length [A] {IA}.




(* ---------------------------------------------------------------------- *)
(** * Update *)

Section Update.
Context (A:Type) {IA: Inhab A}.
Implicit Types n : nat.
Implicit Types x v : A.
Implicit Types l : list A.

Fixpoint update n v l { struct l } : list A :=
  match l with
  | nil => nil
  | x::l' =>
     match n with
     | 0 => v::l'
     | S n' => x::update n' v l'
     end
  end.

Lemma update_nil : forall n v,
  update n v nil = nil.
Proof using. auto. Qed. 

Lemma update_cons_match : forall n v x l,
  update n v (x::l) = 
    match n with
    | 0 => v::l
    | S n' => x::(update n' v l)
    end.
Proof using. auto. Qed.

Lemma update_zero : forall v x l,
  update 0 v (x::l) = v::l.
Proof using. auto. Qed.

Lemma update_succ : forall n v x l,
  update (S n) v (x::l) = x::(update n v l).
Proof using. auto. Qed.

Definition update_cons := update_succ.

Lemma update_cons_pos : forall n v x l,
  n > 0 ->
  update n v (x::l) = x::(update (n-1) v l).
Proof using.
  intros. destruct n.
  { math. }
  { rewrite~ update_succ. fequals_rec. math. }
Qed.

Lemma update_app_r : forall m l1 l2 n v,
  n = length l1 + m ->
  update n v (l1 ++ l2) = l1 ++ update m v l2.
Proof.
  intros m l1. gen m. induction l1 as [| x l1' ]; introv E; rew_list in *.
  { fequals. math. }
  { math_rewrite (n = S (length l1' + m)). rewrite update_cons.
    fequals. erewrite* IHl1'. }
Qed.

Lemma update_prefix_length : forall l1 l2 x v,
  update (length l1) v (l1 ++ x :: l2) = l1 & v ++ l2.
Proof.
  intros. rewrite app_assoc. rewrites (>> update_app_r 0).
  { math. } { rew_list~. }
Qed.

Lemma update_ge_length : forall n v l,
  n >= length l ->
  update n v l = l.
Proof.
  introv E. gen n. induction l; rew_list; intros.
  { auto. }
  { rewrite update_cons_pos; [|math]. fequals. applys IHl. math. }
Qed.

Lemma length_update : forall n v l, 
  length (update n v l) = length l.
Proof using.
  intros. gen n. induction l; intros.
  { auto. } 
  { destruct n as [|n'].
    { rewrite update_zero. rew_list~. }
    { rewrite update_succ. rew_list. rewrite~ IHl. } }
Qed.

Lemma nth_update_eq : forall n l v,
  n < length l ->
  nth n (update n v l) = v.
Proof using.
  intros n l. gen n. induction l; introv N; rew_list in N. 
  { false. math. }
  { destruct n as [|n'].
    { rewrite update_zero. rew_listx~. }
    { rewrite update_cons. rew_listx. applys* IHl. math. } }
Qed.

Lemma nth_update_neq : forall n m l v,
  m < length l -> 
  n <> m ->
  nth n (update m v l) = nth n l.
Proof using.
  intros n m l. gen n m. induction l; introv B N; rew_list in B.
  { false. math. }
  { destruct m as [|m'].
    { rewrite update_zero. do 2 (rewrite nth_pos; [|math]). auto. }
    { rewrite update_succ. destruct n as [|n'].
      { rew_listx~. }
      { rew_listx. applys~ IHl. math. } } }
Qed.

End Update.

Opaque update.


(* ---------------------------------------------------------------------- *)
(** * Make *)

Section Make.
Context (A:Type) {IA:Inhab A}.
Implicit Types i n : nat.
Implicit Types v : A.
Implicit Types l : list A.

Fixpoint make (n:nat) (v:A) : list A :=
   match n with
   | 0 => nil
   | S n' => v :: make n' v
   end.

Lemma make_zero : forall v,
  make 0 v = nil.
Proof using. auto. Qed.

Lemma make_succ : forall n v,
  make (S n) v = v::(make n v).
Proof using. auto. Qed.

Lemma make_pos : forall n v,
  n > 0 ->
  make n v = v::(make (n-1) v).
Proof using.
  introv E. destruct n.
    math.
    rewrite make_succ. fequals_rec. math. 
Qed.

Lemma nth_make : forall i n v,
  i < n -> 
  nth i (make n v) = v.
Proof using.
  introv. gen n; induction i; introv E.
  destruct n. math. auto.
  destruct n. math. rewrite make_succ. rewrite nth_succ. rewrite~ IHi. math.
Qed.

Lemma length_make : forall n v,
  length (make n v) = n.
Proof using.
  intros. induction n.
  auto.
  rewrite make_succ. rewrite length_cons. math.
Qed.

End Make.

Opaque make.




(* ********************************************************************** *)
(** * Other definitions and results *)


(* ---------------------------------------------------------------------- *)
(* ** Function for mapping partial function on lists *)

Definition map_partial (A B : Type) (f : A -> option B) :=
  fix aux (l : list A) : option (list B) := match l with
    | nil => Some nil
    | x::l' => LibOption.apply_on (f x) (fun v =>
                 LibOption.map (cons v) (aux l'))
   end.


(* ---------------------------------------------------------------------- *)
(* ** Induction principle on lists *)

Section ListSub.
Variable (A:Type).

(** Immediate sub-list well-founded order *)

Inductive list_sub : list A -> list A -> Prop :=
  | list_sub_cons : forall x l,
      list_sub l (x::l).

Hint Constructors list_sub.
Lemma list_sub_wf : wf list_sub.
Proof using.
  intros l. induction l;
  apply Acc_intro; introv H; inverts~ H.
Qed.

End ListSub.

Implicit Arguments list_sub [[A]].
Hint Constructors list_sub.
Hint Resolve list_sub_wf : wf.

(** Induction on all but last item *)

Lemma list_ind_last : forall (A : Type) (P : list A -> Prop),
  P nil ->
  (forall (a : A) (l : list A), P l -> P (l & a)) ->
  forall l : list A, P l.
Proof using.
  introv H1 H2. intros. induction_wf IH: (measure_wf (@length A)) l.
  lets [E|(x&l'&E)]: (last_case l); subst. auto.
  unfolds measure. rewrite length_last in IH. auto with maths.
Qed.





(* ********************************************************************** *)
(** * Properties of predicate on lists *)


(* ---------------------------------------------------------------------- *)
(* ** Forall *)

(** [Forall P L] asserts that all the elements in the list [L]
    satisfy the predicate [P]. *)

Inductive Forall A (P:A->Prop) : list A -> Prop :=
  | Forall_nil :
      Forall P nil
  | Forall_cons : forall l x,
      P x -> Forall P l ->
      Forall P (x::l).

Section ForallProp.
Variables A : Type.
Implicit Types l : list A.
Implicit Types P : A->Prop.

Hint Constructors Forall.

Lemma Forall_app : forall P l1 l2,
  Forall P l1 -> Forall P l2 ->
  Forall P (l1 ++ l2).
Proof using. introv H Px. induction H; rew_app; auto. Qed.

Lemma Forall_app_inv : forall P l1 l2,
  Forall P (l1 ++ l2) ->
  Forall P l1 /\ Forall P l2.
Proof using.
  intros. induction l1. auto.
  rew_app in H. inverts* H.
Qed.

Lemma Forall_last : forall P l x,
  Forall P l -> P x ->
  Forall P (l & x).
Proof using. intros. apply~ Forall_app. Qed.

Lemma Forall_last_inv : forall P l x,
  Forall P (l & x) ->
  Forall P l /\ P x.
Proof using.
  introv H. induction l.
  inverts* H.
  rew_list in *. inverts H. forwards*: IHl.
Qed.

Lemma Forall_weaken : forall P Q l,
  Forall P l -> pred_le P Q ->
  Forall Q l.
Proof using. induction l; introv H L; inverts* H. Qed.

Lemma Forall_inv_tail : forall (P : A -> Prop) (a : A) (l : list A),
  Forall P (a :: l) -> Forall P l.
Proof using. introv F. inverts~ F. Qed.

Lemma Forall_inv_head : forall (P : A -> Prop) (a : A) (l : list A),
  Forall P (a :: l) -> P a.
Proof using. introv F. inverts~ F. Qed.

Lemma Forall_inv : forall (P : A -> Prop) (a : A) (l : list A),
  Forall P (a :: l) -> P a /\ Forall P l.
Proof using. introv F. inverts~ F. Qed.

Lemma Forall_iff_forall_mem : forall (P : A -> Prop) (l : list A),
  Forall P l <-> (forall x : A, mem x l -> P x).
Proof using.
  introv. induction l; iff I.
   introv IN. false.
   constructors.
   introv IN. rew_mem in IN. rew_refl in IN.
    inverts IN; inverts~ I. apply~ IHl.
   constructors.
    apply I. rew_mem in *. auto.
    apply~ IHl. introv IN. apply~ I. rew_mem. rew_refl*.
Qed.

Lemma Forall_mem : forall (P : A -> Prop) l a,
  Forall P l ->
  mem a l ->
  P a.
Proof using. introv F I. rewrite Forall_iff_forall_mem in F. apply~ F. Qed.

End ForallProp.

Section ForallToConj.
Variables (A : Type) (P : A->Prop).
Hint Constructors Forall.
Ltac forall_to_conj_prove :=
  extens; iff H;
  repeat (match goal with H: Forall _ _ |- _ => inversion H end);
  repeat (first [constructor | auto_star ]).

Lemma Forall_to_conj_1 : forall x1,
  Forall P (x1::nil) = (P x1).
Proof using. forall_to_conj_prove. Qed.

Lemma Forall_to_conj_2 : forall x1 x2,
  Forall P (x1::x2::nil) = (P x1 /\ P x2).
Proof using. forall_to_conj_prove. Qed.

Lemma Forall_to_conj_3 : forall x1 x2 x3,
  Forall P (x1::x2::x3::nil) = (P x1 /\ P x2 /\ P x3).
Proof using. forall_to_conj_prove. Qed.

Lemma Forall_to_conj_4 : forall x1 x2 x3 x4,
  Forall P (x1::x2::x3::x4::nil) = (P x1 /\ P x2 /\ P x3 /\ P x4).
Proof using. forall_to_conj_prove. Qed.

End ForallToConj.

Hint Resolve has_pair_here has_pair_next.

Global Instance Forall_decidable : forall (A : Type) (P : A->Prop) (l : list A),
  (forall x, Decidable (P x)) -> Decidable (Forall P l).
Proof using.  (*todo: optimize proof *)
  introv H. applys decidable_make
    (fold_left (fun a b => and b (decide (P a))) true l).
  tests: (Forall P l).
   rewrite~ isTrue_true. fold_bool.
    induction~ C. rew_list. (* TODO: rewrite neutral_l_and. *) simpl. case_if~.
   rewrite~ isTrue_false. fold_bool.
    induction~ l.
     false C. constructor~.
     rew_list. simpl. case_if~.
      apply~ IHl. intro F; apply C. constructor~.
      clear C IHl. induction* l.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Forall2 *)

(** [Forall2 P L1 L2] asserts that the lists [L1] and [L2]
    have the same length and that elements at corresponding
    indices are related by the binary relation [P]. *)

Inductive Forall2 A B (P:A->B->Prop) : list A -> list B -> Prop :=
  | Forall2_nil :
      Forall2 P nil nil
  | Forall2_cons : forall l1 l2 x1 x2,
      P x1 x2 -> Forall2 P l1 l2 ->
      Forall2 P (x1::l1) (x2::l2).

Section PropProperties2.
Variables A B : Type.
Implicit Types l : list A.
Implicit Types r : list B.
Implicit Types P : A -> B -> Prop.
Hint Constructors Forall2.

Lemma Forall2_app : forall P l1 l2 r1 r2,
      Forall2 P l1 r1 -> Forall2 P l2 r2 ->
      Forall2 P (l1 ++ l2) (r1 ++ r2).
Proof using. introv H H'. induction H; rew_app; auto. Qed.

Lemma Forall2_last : forall P l r x1 x2,
      Forall2 P l r -> P x1 x2 ->
      Forall2 P (l & x1) (r & x2).
Proof using. intros. apply~ Forall2_app. Qed.

Lemma Forall2_last_inv : forall P l1 r' x1,
  Forall2 P (l1 & x1) r' ->
  exists (r2:list A2) x2,
  r' = r2 & x2 /\ P x1 x2 /\ Forall2 P l1 r2.
Proof using.
  introv H. sets_eq l': (l1&x1). gen l1 x1.
  induction H; intros; subst.
  false* nil_eq_last_inv.
  destruct l0; rew_app in EQl'; inverts EQl'.
    inverts H0. exists~ (@nil A2) x2.
    forwards~ (r2'&x2'&?&?&?): IHForall2. subst. exists~ (x2::r2') x2'.
Qed.

Lemma Forall2_length : forall P l r,
  Forall2 P l r -> length l = length r.
Proof using.
  introv H. induction H. simple~.
  do 2 rewrite~ length_cons.
Qed.

Lemma Forall2_take : forall P n l r,
  Forall2 P l r ->
  Forall2 P (take n l) (take n r).
Proof using. induction n; introv H; inverts H; simple~. Qed.

Hint Constructors Forall2.
Hint Resolve Forall2_last.

Lemma Forall2_rev : forall P l r,
  Forall2 P l r -> Forall2 P (rev l) (rev r).
Proof using. induction l; introv M; inverts M; rew_rev; auto. Qed.

Lemma Forall2_weaken : forall A B (P Q : A -> B -> Prop) la lb,
  Forall2 P la lb ->
  (forall a b, P a b -> Q a b) ->
  Forall2 Q la lb.
Proof using. introv F W. induction F; constructors~. Qed.

Lemma Forall2_forall_Nth : forall A B (P : A -> B -> Prop) la lb,
  Forall2 P la lb -> forall n a b,
    Nth n la a ->
    Nth n lb b ->
    P a b.
Proof using. introv F N1 N2. gen n. induction~ F; introv N1 N2; inverts N1; inverts* N2. Qed.

Lemma Forall2_swap : forall (P : A1 -> A2 -> Prop) l r,
  Forall2 P l r ->
  Forall2 (fun b a => P a b) r l.
Proof using. introv F. induction~ F; constructors~. Qed.

Lemma Forall2_map : forall f (P : A1 -> A2 -> Prop) l,
  (forall a, P a (f a)) ->
  Forall2 P l (map f l).
Proof using. introv I. induction l; constructors~. Qed.

End PropProperties2.

Implicit Arguments Forall2_last_inv [A1 A2 P l1 r' x1].

(* todo : inversion lemmas for other predicates *)


Lemma map_partial_inv : forall (A B:Type) (f: A->option B) lx ly,
  map_partial f lx = Some ly ->
  Forall2 (fun x y => f x = Some y) lx ly.
Proof using.
  induction lx; simpl map_partial; introv Eq.
   inverts Eq. apply Forall2_nil.
   lets fa Fa Eq2: (apply_on_inv Eq).
    lets ly1 Eqly ?: (map_on_inv Eq2). subst ly.
    apply* Forall2_cons.
Qed.

Implicit Arguments map_partial_inv [A B f lx ly].


(* ---------------------------------------------------------------------- *)
(* ** Forall3 *)

(** [Forall3] is similar to [Forall2] except that it relates three lists. *)

Inductive Forall3 A B C (P : A -> B -> C -> Prop)
  : list A -> list B -> list C -> Prop :=
  | Forall3_nil :
      Forall3 P nil nil nil
  | Forall3_cons : forall l1 l2 l3 x1 x2 x3,
      P x1 x2 x3 -> Forall3 P l1 l2 l3 ->
      Forall3 P (x1::l1) (x2::l2) (x3::l3).


(* ---------------------------------------------------------------------- *)
(* ** Exists *)

(** [exists P L] asserts that there exists a value in the
    list [L] that satisfied the predicate [P]. *)

Inductive Exists A (P:A->Prop) : list A -> Prop :=
  | Exists_here : forall l x,
      P x -> Exists P (x::l)
  | Exists_next : forall l x,
      Exists P l ->
      Exists P (x::l).

Section ExistsProp.
Variables A : Type.
Implicit Types l : list A.
Implicit Types P : A -> Prop.

Lemma Exists_nil_inv : forall P,
  Exists P nil -> False.
Proof using. introv H. invert* H. Qed.

Lemma Exists_cons_inv : forall P l x,
  Exists P (x::l) -> P x \/ Exists P l.
Proof using. induction l; introv H; inverts~ H. Qed.

Global Instance Exists_decidable : forall P l,
    (forall a : A, Decidable (P a)) ->
    Decidable (Exists P l).
  introv D. induction l.
   applys decidable_make false. fold_bool. rew_refl. intro Abs. inverts Abs.
   applys decidable_make (decide (P a \/ Exists P l)).
    rewrite decide_spec. rewrite isTrue_eq_isTrue. iff I.
     inverts I as I.
      apply~ Exists_here.
      apply~ Exists_next.
     inverts I as I.
      left~.
      right~.
Defined.

Lemma Exists_iff_exists_mem : forall P l,
  Exists P l <-> exists (a : A), mem a l /\ P a.
Proof using.
  introv. iff E; induction l; inverts E as E.
   exists a. splits~. simpl. rew_refl. left~.
   forwards~ (a'&I&H): (rm IHl) (rm E). exists a'. splits~.
    simpl. rew_refl. right~.
   false*.
   simpl in E. rew_refl in E. lets ([I|I]&H): (rm E).
    substs. apply~ Exists_here.
    apply~ Exists_next. apply* IHl.
Qed.

Lemma Exists_exists_st : forall P l,
  Exists P l <-> exists_st P l.
Proof using.
  introv. iff E.
   induction l.
    inverts E.
    unfolds. rewrite fold_right_cons. rew_refl.
     forwards [Pa|Nl]: Exists_cons_inv E; [right~|left~].
   induction l.
    compute in E. false*.
    unfolds in E. rewrite fold_right_cons in E. rew_refl in E.
     inverts E as E.
      apply~ Exists_next.
      apply~ Exists_here.
Qed.

Lemma Exists_weaken : forall P Q l,
  Exists P l -> pred_le P Q ->
  Exists Q l.
Proof using.
  introv E Impl. rewrite Exists_iff_exists_mem in *.
  lets (a&I&H): (rm E). exists a. splits*.
Qed.

Lemma Exists_split : forall P l,
  Exists P l ->
  exists l1 x l2, l = l1 ++ x :: l2
    /\ Forall (fun x => ~ P x) l1
    /\ P x.
Proof using.
  introv E. induction E.
   exists (@nil A) x l. splits~. constructors~.
   lets (l1&x'&l2&E1&F&HP): (rm IHE). tests Px: (P x).
    exists (@nil A) x l. splits~. constructors~.
    substs. exists (x :: l1) x' l2. splits~. constructors~.
Qed.

End ExistsProp.




Lemma mem_split : forall A l (x:A),
  mem x l ->
  exists l1 l2,
    l = l1 ++ x :: l2 /\ ~ mem x l1.
Proof using.
  introv M. forwards (l1&?&l2&E&NF&?): Exists_split (fun y => x = y).
   rewrite Exists_iff_exists_mem. exists x. splits*.
   substs. rewrite Forall_iff_forall_mem in NF. exists* l1 l2.
Qed.

Lemma map_partial_inv_none : forall (A B:Type) (f: A->option B) l,
  map_partial f l = None ->
  Exists (fun x => f x = None) l.
Proof using.
  induction l; simpl map_partial; introv Eq; tryfalse.
  forwards [E|(b&E1&E2)]: apply_on_inv_none Eq.
   apply* Exists_here.
   apply Exists_next. apply~ IHl. destruct~ map_partial. false*.
Qed.

Lemma map_partial_none : forall (A B:Type) (f: A->option B) l,
  Exists (fun x => f x = None) l ->
  map_partial f l = None.
Proof using.
  induction l; simpl map_partial; introv Eq; inverts Eq as Eq.
   rewrite~ Eq.
   destruct~ (f a). rewrite~ IHl.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Exists2 *)

(** [Exists2 P L1 L2] asserts that there exists an index [n]
    such that the n-th element of [L1] and the n-th element
    of [L2] are related by the binary relation [P]. *)

Inductive Exists2 A1 A2 (P : A1 -> A2 -> Prop)
  : list A1 -> list A2 -> Prop :=
  | Exists2_here : forall l1 l2 x1 x2,
      P x1 x2 -> Exists2 P (x1::l1) (x2::l2)
  | Exists2_next : forall l1 l2 x1 x2,
      Exists2 P l1 l2 ->
      Exists2 P (x1::l1) (x2::l2).







(* ---------------------------------------------------------------------- *)
(** * Fold *)

Section Fold.
Variables (A B:Type) (m:monoid_def B) (L:list A) (f:A->B).

Definition fold A B (m:monoid_def B) (f:A->B) (L:list A) : B :=
  fold_right (fun x acc => monoid_oper m (f x) acc) (monoid_neutral m) L.

Lemma fold_nil :
  fold m f nil = monoid_neutral m.
Proof using. auto. Qed.
Lemma fold_cons : forall x l,
  fold m f (x::l) = monoid_oper m (f x) (fold m f l) .
Proof using. auto. Qed.
Lemma fold_app : forall l1 l2,
  Monoid m ->
  fold m f (l1 ++ l2) = monoid_oper m (fold m f l1) (fold m f l2).
Proof using.
  unfold fold. intros. rewrite fold_right_app. gen l2.
  induction l1; intros.
  repeat rewrite fold_right_nil. rewrite~ monoid_neutral_l.
  repeat rewrite fold_right_cons. rewrite <- monoid_assoc. fequals.
Qed.
Lemma fold_last : forall x l,
  Monoid m ->
  fold m f (l & x) = monoid_oper m (fold m f l) (f x).
Proof using.
  intros. rewrite~ fold_app. rewrite fold_cons.
  rewrite fold_nil. rewrite monoid_neutral_r. auto.
Qed.
End Fold.

Opaque fold.

(* TODO: migrate [fold_pointwise] here, after moving [Mem]. *)


Lemma fold_congruence : forall A B (m : monoid_def B) (f g : A -> B) (xs : list A),
  (forall x, Mem x xs -> f x = g x) ->
  fold m f xs = fold m g xs.
Proof using.
  unfold fold.
  induction xs as [| x xs ]; intros; simpl.
  { eauto. }
  { f_equal; eauto. }
Qed.

(* Reasoning about an arbitrary relation under a [fold]. *)

Lemma fold_pointwise:
  forall B (m : monoid_def B) (leB : B -> B -> Prop),
  Monoid m ->
  refl leB ->
  Proper (leB ++> leB ++> leB) (monoid_oper m) ->
  forall A (L : list A),
  forall (f f' : A -> B),
  (forall x, Mem x L -> leB (f x) (f' x)) ->
  leB (fold m f L) (fold m f' L).
Proof using.
  introv HM HR HP. induction L; introv HL.
  do 2 rewrite fold_nil. applys HR.
  do 2 rewrite fold_cons. apply HP. applys~ HL. applys~ IHL.
Qed.

Lemma fold_equiv_step : forall A B (m:monoid_def B) (f:A->B) (L: list A) a,
  Monoid_commutative m ->
  No_duplicates L ->
  Mem a L ->
  exists L',
     fold m f L = fold m f (a::L')
  /\ (forall x, Mem x L <-> Mem x (a::L'))
  /\ No_duplicates (a::L').
Proof using.
  introv Hm. induction L as [|b T]; introv DL La. inverts La.
  tests: (a = b).
    exists T. splits*.
    inverts La. false. inverts DL as DLb DT. forwards~ (L'&EL'&EQ&DL'): IHT.
     exists (b::L'). splits.
       do 3 rewrite fold_cons. rewrite EL'.
        rewrite fold_cons. do 2 rewrite monoid_assoc.
        rewrite~ (monoid_comm (f b)).
       intros x. specializes EQ x. rewrite Mem_cons_eq in EQ.
        do 3 rewrite Mem_cons_eq. autos*.
       inverts DL'. constructors.
         introv N. inverts N. false. false.
         constructors~. introv N. applys DLb. rewrite EQ. constructors~.
Qed.

Lemma fold_equiv : forall A B (m:monoid_def B) (f:A->B) (L1 L2: list A),
  Monoid_commutative m ->
  No_duplicates L1 ->
  No_duplicates L2 ->
  (forall x, Mem x L1 <-> Mem x L2) ->
  fold m f L1 = fold m f L2.
Proof using.
  induction L1; introv HM D1 D2 EQ.
  cuts_rewrite (L2 = nil). rewrite~ fold_nil.
    destruct L2; auto. forwards~ M: (proj2 (EQ a)). inverts M.
  inverts D1. asserts L2a: (Mem a L2). rewrite~ <- EQ.
   forwards* (L2'&V2'&EQ'&D2'): fold_equiv_step f L2a.
   rewrite V2'. do 2 rewrite fold_cons.
  inverts D2'.
  rewrite~ (IHL1 L2'). intros.
  tests: (x = a).
    iff; auto_false*.
  asserts_rewrite (Mem x L1 = Mem x (a::L1)).
    extens. iff~ M. inverts~ M. false.
  asserts_rewrite (Mem x L2' = Mem x (a::L2')).
    extens. iff~ M. inverts~ M. false.
  rewrite EQ. rewrite* EQ'.
Qed.



(* ---------------------------------------------------------------------- *)
(* ** Remove_duplicates *)

(** [Remove_duplicates L] produces a list [L'] that is the sublist of [L]
    obtained by keeping only the first occurence of every item. *)

Fixpoint Remove_duplicates A (L:list A) :=
  match L with
  | nil => nil
  | x::L' => x :: (Filter (<> x) (Remove_duplicates L'))
  end.

Lemma Remove_duplicates_spec : forall A (L L':list A),
  L' = Remove_duplicates L ->
     No_duplicates L'
  /\ (forall x, Mem x L' <-> Mem x L)
  /\ (length L' <= length L)%nat.
Proof using.
  Hint Constructors Mem No_duplicates.
  introv E.
  asserts (R1&R2): (No_duplicates L' /\ (forall x, Mem x L' <-> Mem x L)).
  gen L' E. induction L; introv E; simpls.
  subst. splits*.
  sets_eq L'': (Remove_duplicates L). forwards~ [E' M]: IHL. splits~.
    subst L'. constructors. applys Filter_neq. applys* No_duplicates_Filter.
    subst L'. intros x. lets (M1&M2): M x. iff N.
      inverts N as R. auto. lets: Filter_Mem_inv R. constructors*.
      lets [E|(H1&H2)]: Mem_inv N. subst*. constructors. applys* Filter_Mem.
  splits~. applys~ No_duplicates_length_le. introv Hx. rewrite~ <- R2.
Qed.

Lemma Remove_duplicates_mem : forall A (L:list A) a,
  mem a (Remove_duplicates L) = mem a L.
Proof using. introv. extens. repeat rewrite <- Mem_mem. apply~ Remove_duplicates_spec. Qed.



(* ---------------------------------------------------------------------- *)
(* ** Update as a relation *)

(** [Update n x L L'] asserts [L'] is the list obtained by substituting
    in [L] the item at index [n] with [x]. *)

Definition Update A (n:nat) (x:A) l l' :=
    length l' = length l
  /\ (forall y m, Nth m l y -> m <> n -> Nth m l' y)
  /\ Nth n l' x.

Section Update.
Variables A : Type.
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types n : nat.
Hint Constructors Nth.

Lemma Update_zero : forall x y l,
  Update 0 x (y::l) (x::l).
Proof using.
  intros. splits.
  rew_length~.
  introv M H. inverts* M.
  autos*.
Qed.

Lemma Update_cons : forall i x y l l',
  Update i x l l' -> 
  Update (S i) x (y::l) (y::l').
Proof using.
  introv (L&O&E). splits.
  rew_length~.
  introv M H. inverts* M.
  autos*.
Qed.

Definition Update_succ := Update_cons.

Lemma Update_app_l : forall i x l1 l1' l2,
  Update i x l1 l1' -> 
  Update i x (l1++l2) (l1'++l2).
Proof using.
  introv (L&O&E). splits.
  rew_length~.
  introv M H. destruct (Nth_app_inv _ _ M).
    apply~ Nth_app_l.
    unpack. apply* Nth_app_r. math.
  apply~ Nth_app_l.
Qed.

Lemma Update_app_r : forall i j x l1 l2 l2',
  Update j x l2 l2' -> 
  i = (j + length l1)%nat -> 
  Update i x (l1++l2) (l1++l2').
Proof using.
  introv (L&O&E) Eq. splits.
  rew_length~.
  introv M H. destruct (Nth_app_inv _ _ M).
    apply~ Nth_app_l.
    unpack. apply* Nth_app_r. apply* O. math. math.
  apply* Nth_app_r.
Qed.

Lemma Update_length : forall i x l l',
  Update i x l l' -> 
  length l = length l'.
Proof using. introv (L&O&E). auto. Qed.

Lemma Update_not_nil_l : forall i x l1 l2,
  Update i x l1 l2 -> 
  l1 <> nil.
Proof using. introv (L&O&E) K. subst. inverts E. Qed.

Lemma Update_not_nil_r : forall i x l1 l2,
  Update i x l1 l2 -> 
  l2 <> nil.
Proof using. introv (L&O&E) K. subst. inverts E. Qed.

End Update.


(* ---------------------------------------------------------------------- *)
(* ** Assoc as a relation *)

(** [Assoc x v l] asserts that [(x,v)] the first pair of the
    form [(x,_)] in [l] *)

Inductive Assoc A B (x:A) (v:B) : list (A*B) -> Prop :=
  | Assoc_here : forall l ,
      Assoc x v ((x,v)::l)
  | Assoc_next : forall y l (w:B),
      Assoc x v l -> x <> y ->
      Assoc x v ((y,w)::l).



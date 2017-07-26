(**************************************************************************
* TLC: A library for Coq                                                  *
* Lists                                                                   *
* See also LibListExec.v and LibListSub.v                                 *
***************************************************************************)

Set Implicit Arguments.
Require Import Coq.Classes.Morphisms. (* for [Proper] instances *)
Require Import LibTactics LibLogic LibReflect LibOperation
 LibProd LibOption LibNat LibInt LibWf LibMonoid LibRelation.
Generalizable Variables A B.
Local Open Scope nat_scope.
Local Open Scope comp_scope.
Global Close Scope list_scope.


(* ********************************************************************** *)
(** Fixing implicit arguments *)

(* From Prelude:

Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.
*)

Arguments nil {A}.
Arguments cons {A}.

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

Instance Inhab_list : forall A, Inhab (list A).
Proof using. intros. apply (Inhab_of_val nil). Qed.



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
(** ** [rew_listx] for all other operations on lists *)

Tactic Notation "rew_listx" :=
  autorewrite with rew_listx.
Tactic Notation "rew_listx" "~" :=
  rew_listx; auto_tilde.
Tactic Notation "rew_listx" "*" :=
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



(* ********************************************************************** *)
(** * Properties of operations *)

(* ---------------------------------------------------------------------- *)
(** ** Definitions of Fold-right and App *)

Fixpoint fold_right A B (f:A->B->B) (i:B) (l:list A) :=
  match l with
  | nil => i
  | x::L' => f x (fold_right f i L')
  end.

Definition app A (l1 l2 : list A) :=
  fold_right (fun x (acc:list A) => x::acc) l2 l1.

(* Properties appear further *)

(** [l1 ++ l2] concatenates two lists *)

Infix "++" := app (right associativity, at level 60) : liblist_scope.

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

(* [app_cons_r] further below *)

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

Lemma app_cons_one_r : forall x l,
  (x::nil) ++ l = x::l.
Proof using. auto. Qed.

Lemma app_cons_one_l : forall x l,
  l ++ (x::nil) = l&x. (* equal up to notation *)
Proof using. auto. Qed.

Lemma app_last_l : forall x l1 l2,
  (l1 & x) ++ l2 = l1 ++ (x::l2).
Proof using. intros. rewrite~ <- app_cons_r. Qed.

Lemma app_last_r : forall x l1 l2,
  l1 ++ (l2 & x) = (l1 ++ l2) & x.
Proof using. intros. rewrite~ <- app_assoc. Qed.

(* last *)

Lemma last_nil : forall x,
  nil & x = x::nil.
Proof using. auto. Qed.

(* same as [app_cons_l] *)
Lemma last_cons : forall x y l,
  (x::l) & y = x::(l&y).
Proof using. auto. Qed.

Lemma last_one : forall x y,
  (x::nil) & y = x::y::nil.
Proof using. auto. Qed.

(* same as [app_last_r] *)
Lemma last_app : forall x l1 l2,
  (l1 ++ l2) & x = l1 ++ (l2 & x).
Proof using. intros. rewrite~ app_last_r. Qed.

End App.

Opaque app.

Hint Rewrite app_cons_l app_nil_l app_nil_r app_assoc
  app_cons_one_r : rew_list.
(* Note: [app_last_l] may be safely added to [rew_list] *)

Hint Rewrite app_cons_l app_nil_l app_nil_r app_assoc
  app_cons_one_r : rew_listx.

Hint Rewrite app_cons_l app_nil_l app_nil_r app_assoc
  app_cons_one_r : rew_lists.


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

Fixpoint fold_left A B (f:A->B->B) (i:B) (l:list A) : B :=
  match l with
  | nil => i
  | x::L' => fold_left f (f x i) L'
  end.

Section FoldLeft.
Variables A B : Type.
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types (f : A -> B -> B) (i : B).

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

Definition length A (l:list A) : nat :=
  fold_right (fun x acc => 1+acc) 0 l.

Section Length.
Variables (A : Type).
Implicit Types l : list A.

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
(** * Inversion lemmas for structural composition *)

Section AppInversion.
Variables A : Type.
Implicit Types x : A.
Implicit Types l : list A.

(**------- Length -------- *)

(* -- TODO: should this be length_eq_zero? or length_zero can be
      read as "having the length-zero property"? *)

Lemma length_zero_inv : forall l,
  length l = 0%nat ->
  l = nil.
Proof using.
  intros l. destruct l; rew_list; introv E. { auto. } { false. }
Qed.

Lemma length_zero_eq_eq_nil : forall l,
  (length l = 0) = (l = nil).
Proof using.
  extens. iff M. destruct l; rew_list; auto_false*. { subst*. }
Qed.

Lemma length_neq_inv : forall l1 l2,
  length l1 <> length l2 -> 
  (l1 <> l2).
Proof using. introv N E. subst*. Qed.

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
  intros l. induction l; rew_list; introv H.
  { false. math. }
  { destruct l.
    { exists~ a (@nil A). }
    { destruct IHl as (x&l'&E).
      { rew_list in *. math. }
      { exists x (a::l'). rewrite~ E. } } }
Qed.

(**------- Cons -------- *)

Lemma cons_case : forall l,
  l = nil \/ exists x l', l = x :: l'.
Proof using. intros. destruct* l. Qed.

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
Proof using. introv N. destruct* l. Qed.

Lemma cons_eq_cons_inv : forall x1 x2 l1 l2,
  x1 :: l1 = x2 :: l2 -> 
  x1 = x2 /\ l1 = l2.
Proof using. introv H. inverts* H. Qed.

(**------- App -------- *)

Lemma app_eq_nil_inv : forall l1 l2,
  l1 ++ l2 = nil -> 
  l1 = nil /\ l2 = nil.
Proof using. intros. destruct l1; destruct l2; intros; tryfalse~; auto. Qed.

(* symmetric of previous lemma *)
Lemma nil_eq_app_inv : forall l1 l2,
  nil = l1 ++ l2 ->
  l1 = nil /\ l2 = nil.
Proof using. intros. symmetry in H. apply* app_eq_nil_inv. Qed.

Lemma app_not_empty_l : forall l1 l2,
  l1 <> nil -> 
  l1 ++ l2 <> nil.
Proof using. introv NE K. apply NE. forwards*: app_eq_nil_inv K. Qed.

Lemma app_not_empty_r : forall l1 l2,
  l2 <> nil -> 
  l1 ++ l2 <> nil.
Proof using. introv NE K. apply NE. forwards*: app_eq_nil_inv K. Qed.

Lemma app_l_eq_self_inv : forall l1 l2,
  l1 ++ l2 = l1 -> 
  l2 = nil.
Proof using.
  introv E. apply length_zero_inv.
  lets: (args_eq_1 (@length A) E). rew_list in H. math.
Qed.

(* symmetric of previous lemma *)
Lemma self_eq_app_l_inv : forall l1 l2,
  l1 = l1 ++ l2 -> 
  l2 = nil.
Proof using. intros. applys* app_l_eq_self_inv. Qed.

Lemma app_r_eq_self_inv : forall l1 l2,
  l1 ++ l2 = l2 -> 
  l1 = nil.
Proof using.
  introv E. apply length_zero_inv.
  lets: (args_eq_1 (@length A) E). rew_list in H. math.
Qed.

(* symmetric of previous lemma *)
Lemma self_eq_app_r_inv : forall l1 l2,
  l2 = l1 ++ l2 -> 
  l1 = nil.
Proof using. intros. applys* app_r_eq_self_inv. Qed.


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
  intros l1. induction l1; introv E; rew_list in *.   
  { rewrites~ (>> self_eq_app_r_inv E). }
  { destruct l2; rew_list in *.
    { rewrite <- app_cons_l in E. rewrites~ (>> self_eq_app_r_inv (eq_sym E)). }
    { inverts E. fequals. applys* IHl1. } }
Qed.
  (* Alternative proof using [rev]:
     introv E. lets H: (f_equal (@rev A) E). rew_list in H.
     lets N: app_cancel_l H. applys~ rev_inj. *)


(**------- Last -------- *)

Lemma last_case : forall l,
  l = nil \/ exists x l', l = l' & x.
Proof using.
  intros. destruct l. { left*. }
  { right. forwards* (x&l'&H): (length_pos_inv_last (a::l)).
    rew_list. math. }
Qed.

Lemma last_eq_nil_inv : forall a l,
  l & a = nil -> 
  False.
Proof using. introv E. induction l; rew_list; false. Qed.

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
  introv H. gen l2. induction l1; introv E; rew_list in E.
  { destruct l2; rew_list in E; inverts E as E.
    { auto. } { false nil_eq_last_inv E. } }
  { destruct l2; rew_list in E.
    { inverts E as E. false last_eq_nil_inv E. }
    { inverts E. forwards* [? ?]: IHl1.
     split; congruence. } }
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
  intros. destruct l1; rew_list in H; inverts H. { left~. } { right*. }
Qed.

Lemma last_eq_middle_inv : forall x y l1 l2 l,
  l & x = l1 & y ++ l2 ->
  (l = l1 /\ x = y /\ l2 = nil) \/ (exists l2', l2 = l2'&x).
Proof using.
  introv E. destruct (last_case l2) as [|(z&t&K)].
  { subst. rew_list in *. lets (?&?): last_eq_last_inv E. left*. }
  { subst. repeat rewrite <- app_assoc in E. lets (?&?): last_eq_last_inv E.
    subst. right*. }
Qed.

End AppInversion.

Arguments last_eq_nil_inv [A] [a] [l].
Arguments nil_eq_last_inv [A] [a] [l].
Arguments app_eq_nil_inv [A] [l1] [l2].
Arguments nil_eq_app_inv [A] [l1] [l2].
Arguments nil_eq_middle_inv [A] [x] [l1] [l2].
Arguments cons_eq_middle_inv [A] [x] [y] [l1] [l2] [l].


(* ---------------------------------------------------------------------- *)
(* ** Mem *)

(** [mem x l] asserts that [x] belongs to [l].
    Remark: it could be also defined as [Exists (=x) l]. *)

Inductive mem A (x:A) : list A -> Prop :=
  | mem_here : forall l,
      mem x (x::l)
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
  mem x (y::l) = (x = y \/ mem x l).
Proof using. intros. extens. iff H; inverts* H. Qed.

Lemma mem_cons_eq_cases : forall x y l,
  mem x (y::l) = ((x = y) \/ (x <> y /\ mem x l)).
Proof using.
  intros. extens. tests: (x = y).
  { autos*. }
  { iff H. { inverts~ H. } { destruct H as [|(?&?)]; subst*. } }
Qed.

Lemma mem_one_eq : forall x y,
  mem x (y::nil) = (x = y).
Proof using. intros. extens. iff H; inverts~ H. false_invert. Qed.

Lemma mem_app_eq : forall l1 l2 x,
  mem x (l1 ++ l2) = (mem x l1 \/ mem x l2).
Proof using.
  intros. extens. induction l1; rew_list.
  { split. { auto. } { introv [H|?]. inverts H. auto. } }
  { iff M. 
    { inverts~ M. rewrite IHl1 in H0. destruct* H0. }
    { destruct M. inverts~ H. constructors. rewrite~ IHl1.
      constructors. rewrite~ IHl1. } }
Qed.

Lemma mem_last_eq : forall x y l,
  mem x (l&y) = (mem x l \/ x = y).
Proof using. intros. rewrite mem_app_eq. rewrite~ mem_one_eq. Qed.

Lemma mem_last_eq_cases : forall x y l,
  mem x (l&y) = ((x <> y /\ mem x l) \/ (x = y)).
Proof using.
  intros. extens. induction l; rew_list.  
  (* TODO: redo the proof by induction on the length of the list *)
  { tests: (x = y). { autos*. } 
    { iff M. 
      { inverts~ M. } 
      { destruct M as [(?&H)|]. { inverts~ H. } { subst*. } } } }
  { tests: (x = y). { autos*. }
    { iff M. 
      { inverts M as M'; auto. rewrite IHl in M'. destruct* M'. }
      { destruct M as [(?&H)|].
        { inverts~ H. constructors. rewrite* IHl. }
        { constructors. rewrite~ IHl. } } } }
Qed.

(** Backward *)

Lemma mem_cons : forall l x y,
  x = y \/ mem x l ->
  mem x (y::l).
Proof using. intros. rewrite* mem_cons_eq. Qed.

Lemma mem_cons_l : forall l x,
  mem x (x::l).
Proof using. intros. rewrite* mem_cons_eq. Qed.

Lemma mem_cons_r : forall l x y,
  mem x l ->
  mem x (y::l).
Proof using. intros. rewrite* mem_cons_eq. Qed.

Lemma mem_app : forall l1 l2 x,
  mem x l1 \/ mem x l2 -> 
  mem x (l1 ++ l2).
Proof using. intros. rewrite~ mem_app_eq. Qed.

Lemma mem_app_l : forall l1 l2 x,
  mem x l1 -> 
  mem x (l1 ++ l2).
Proof using. intros. applys* mem_app. Qed.

Lemma mem_app_r : forall l1 l2 x,
  mem x l2 -> 
  mem x (l1 ++ l2).
Proof using. intros. applys* mem_app. Qed.

Lemma mem_last : forall l x y,
  mem x l \/ x = y ->
  mem x (l & y).
Proof using. intros. rewrite* mem_last_eq. Qed.

Lemma mem_last_r : forall l x,
  mem x (l & x).
Proof using. intros. rewrite* mem_last_eq. Qed.

Lemma mem_last_l : forall l x y,
  mem x l ->
  mem x (l & y).
Proof using. intros. rewrite* mem_last_eq. Qed.

(** Inversion *)

Lemma mem_nil_inv : forall x,
  mem x nil ->
  False.
Proof using. introv E. inverts E. Qed.

Lemma mem_cons_inv : forall l x y,
  mem x (y::l) ->
  x = y \/ mem x l.
Proof using. introv E. rewrite* mem_cons_eq in E. Qed.

Lemma mem_cons_inv_cases : forall l x y,
  mem x (y::l) ->
  x = y \/ (x <> y /\ mem x l).
Proof using. introv E. rewrite* mem_cons_eq_cases in E. Qed.

Lemma mem_app_inv : forall x l1 l2,
  mem x (l1 ++ l2) ->
  mem x l1 \/ mem x l2.
Proof using. introv E. rewrite~ mem_app_eq in E. Qed.

Lemma mem_last_inv : forall l x y,
  mem x (l&y) ->
  (x <> y /\ mem x l) \/ x = y.
Proof using. introv E. rewrite* mem_last_eq_cases in E. Qed.

Lemma mem_inv_middle_first : forall l x,
  mem x l ->
  exists l1 l2, l = l1++x::l2 /\ ~ mem x l1.
Proof using.
  introv M. induction M.
  { exists (@nil A) l. rewrite* mem_nil_eq. }
  { tests C: (x=y).
    { exists (@nil A) l. rewrite* mem_nil_eq. }
    { destruct IHM as (l1&l2&E&N). exists (y::l1) l2.
      subst. rew_list. rewrite* mem_cons_eq. } }
Qed.

Lemma mem_inv_middle : forall l x,
  mem x l ->
  exists l1 l2, l = l1++x::l2.
Proof using. introv E. forwards* (?&?&?&?): mem_inv_middle_first E. Qed.

Lemma eq_list_of_not_mem : forall l,
  (forall x, ~ mem x l) ->
  l = nil.
Proof using. introv P. destruct~ l. false P. applys mem_here. Qed.

End Mem.

Hint Rewrite mem_nil_eq mem_cons_eq mem_app_eq mem_last_eq : rew_listx.


(* ---------------------------------------------------------------------- *)
(* ** Nth as a relation *)

(** [Nth n L x] asserts that the n-th element of the list [L]
    exists and is exactly [x] *)

Inductive Nth A : nat -> list A -> A -> Prop :=
  | Nth_zero : forall l x,
      Nth 0 (x::l) x
  | Nth_succ : forall y n l x,
      Nth n l x ->
      Nth (S n) (y::l) x.

Section Nth.
Variables (A : Type).
Implicit Types l : list A.
Implicit Types x : A.
Implicit Types n : nat.
Hint Constructors mem Nth.

Lemma Nth_cons_match : forall n l x y,
  Nth n (y::l) x =
    match n with 
    | O => x = y
    | S n' => Nth (S n') (y::l) x
    end.
Proof using.
  intros. extens. destruct n as [|n'].
  { iff M. inverts~ M. subst~. }
  { iff M. inverts~ M. subst~. }
Qed.

(** --LATER: add [nth_last] lemma *)

Lemma Nth_functional : forall n l x1 x2,
  Nth n l x1 ->
  Nth n l x2 -> 
  x1 = x2.
Proof using. introv H1. induction H1; intro H2; inverts~ H2. Qed.

Lemma Nth_mem : forall l x n,
  Nth n l x -> 
  mem x l.
Proof using. introv N. induction N; autos*. Qed.

Lemma mem_Nth : forall l x,
  mem x l -> 
  exists n, Nth n l x.
Proof using.
  introv H. induction l; rew_listx in *.
  { inverts H. }
  { destruct H. { subst*. } { forwards* (n&?): IHl. } }
Qed.

Lemma Nth_inbound : forall n l x,
  Nth n l x -> 
  n < length l.
Proof using.
  intros n. induction n; introv H; inverts H; rew_list in *.
  { math. }
  { forwards*: IHn. math. }
Qed.

(* TODO: which name for this lemma? *)
Lemma Nth_inbound_inv : forall n l,
  n < length l -> 
  exists x, Nth n l x.
Proof using.
  induction n; introv N; destruct l as [|a l']; rew_list in N; try solve [math].
  { eauto. }
  { simpls. forwards (x&Hx): IHn l'. math. exists x. apply* Nth_succ. }
Qed.

Lemma Nth_app_l : forall n x l1 l2,
  Nth n l1 x -> 
  Nth n (l1 ++ l2) x.
Proof using. intros n. induction n; introv H; inverts H; rew_list*. Qed.

Lemma Nth_app_r : forall n m x l1 l2,
  Nth m l2 x -> 
  Nth (m + length l1)%nat (l1 ++ l2) x.
Proof using.
  intros. gen m. induction l1; introv H; rew_list.
  { applys_eq~ H 3. }
  { applys_eq* Nth_succ 3. }
Qed.

Lemma Nth_app_r' : forall n m x l1 l2,
  Nth m l2 x -> 
  n = (m + length l1)%nat -> 
  Nth n (l1 ++ l2) x.
Proof using. intros. subst. applys* Nth_app_r. Qed.

Lemma Nth_nil_inv : forall n x,
  Nth n nil x -> 
  False.
Proof using. introv H. inverts H. Qed.

Lemma Nth_inv_neq_nil : forall n l x,
  Nth n l x -> 
  l <> nil.
Proof using. introv H. inverts H; auto_false. Qed.

Lemma Nth_cons_inv : forall n x y q,
  Nth n (y::q) x ->
     (n = 0 /\ x = y )
  \/ (exists m, n = m+1 /\ Nth m q x).
Proof using.
  introv H. inverts H. { left*. } { right. exists n0. splits~. math. }
Qed.

Lemma Nth_app_inv : forall n x l1 l2,
  Nth n (l1++l2) x ->
     (Nth n l1 x)
  \/ (exists m, n = length l1 + m /\ Nth m l2 x).
Proof using.
  introv. gen n. induction l1; introv H; rew_list in H.
  { right. rew_list. exists~ n. }
  { inverts H.
    { left~. }
    { forwards* M: IHl1. destruct M as [|(m&?&?)].
      { left~. }
      { right*. rew_list. exists m. split~. math. } } }
Qed.

Lemma Nth_last_inv : forall n x y l,
  Nth n (l&y) x ->
     (Nth n l x)
  \/ (n = length l /\ y = x).
Proof using.
  introv H. lets [|(m&E&F)]: Nth_app_inv H.
  { left~. }
  { right. inverts F as G. { splits~. math. } { inverts G. } }
Qed.

End Nth.


(* ---------------------------------------------------------------------- *)
(** ** [nth_default] as a partial function with a default *)

Fixpoint nth_default A (d:A) (n:nat) (l:list A) {struct l} : A :=
  match l with
  | nil => d
  | x::l' =>
     match n with
     | 0 => x
     | S n' => nth_default d n' l'
     end
  end.

Section NthDef.
Variables (A:Type).
Implicit Types n : nat.
Implicit Types d x : A.
Implicit Types l : list A.
Hint Constructors Nth.

Lemma nth_default_nil : forall n d,
  nth_default d n nil = d.
Proof using. introv. destruct~ n. Qed.

Lemma nth_default_zero : forall x l d,
  nth_default d 0 (x::l) = x.
Proof using. introv. reflexivity. Qed.

Lemma nth_default_succ : forall n x l d,
  nth_default d (S n) (x::l) = nth_default d n l.
Proof using. introv. reflexivity. Qed.

Definition nth_default_cons := nth_default_succ.

Lemma nth_default_gt_length : forall l d n,
  n >= length l ->
  nth_default d n l = d.
Proof using.
  induction l as [|l']; introv N; rew_list in *.
  { auto. }
  { destruct n as [|n']. { false; math. }
    simpl. rewrite~ IHl. math. }
Qed.

Lemma nth_default_of_Nth : forall n l x d,
  Nth n l x -> 
  nth_default d n l = x.
Proof using. introv H. induction~ H. Qed.

Lemma Nth_of_nth_default : forall l d n x,
  nth_default d n l = x ->
  n < length l ->
  Nth n l x.
Proof using.
  intros l. induction l; rew_list; introv E N.
  { false. math. }
  { destruct n; simpls. 
    { subst*. } 
    { constructors. applys* IHl. math. } }
Qed.

End NthDef.

Arguments nth_default [A] : simpl never.

Hint Rewrite nth_default_nil nth_default_zero nth_default_succ : rew_listx.


(* ---------------------------------------------------------------------- *)
(** ** [nth] as a partial function *)

Definition nth `{IA:Inhab A} := 
  nth_default arbitrary.

Section NthFunc.
Context (A:Type) {IA: Inhab A}.
Implicit Types n : nat.
Implicit Types x : A.
Implicit Types l : list A.

Lemma nth_lt_length : forall x l,
  nth 0 (x::l) = x.
Proof using. intros. apply nth_default_zero. Qed.

Lemma nth_zero : forall x l,
  nth 0 (x::l) = x.
Proof using. intros. apply nth_default_zero. Qed.

Lemma nth_succ : forall n x l,
  nth (S n) (x::l) = nth n l.
Proof using. intros. apply nth_default_succ. Qed.

Definition nth_cons := nth_succ.

Lemma nth_cons_case : forall n x l,
  nth n (x::l) = (If n = 0 then x else nth (n-1) l).
Proof using.
  intros. destruct n as [|n'].
  { case_if. rewrite~ nth_zero. }
  { case_if. rewrite~ nth_succ. fequals; math. }
Qed.

Lemma nth_pos : forall n x l,
  n > 0 ->
  nth n (x::l) = nth (n-1) l.
Proof using.
  intros. destruct n. 
  { false. math. } 
  { rewrite nth_succ. fequals. math. } 
Qed.

Lemma nth_gt_length : forall l n,
  n >= length l ->
  nth n l = arbitrary.
Proof using. introv N. applys~ nth_default_gt_length. Qed.

Lemma nth_of_Nth : forall n l x,
  Nth n l x -> 
  nth n l = x.
Proof using. introv H. apply~ nth_default_of_Nth. Qed.

Lemma Nth_of_nth : forall l n x,
  nth n l = x ->
  n < length l ->
  Nth n l x.
Proof using. intros. applys* Nth_of_nth_default. Qed.

Lemma Nth_nth : forall l n,
  n < length l ->
  Nth n l (nth n l).
Proof using. intros. applys* Nth_of_nth. Qed.

Lemma mem_nth : forall l x,
  mem x l -> 
  exists n, nth n l = x.
Proof using.
  intros. forwards [n P]: mem_Nth H. exists n. apply~ nth_of_Nth.
Qed.

Lemma nth_mem : forall n l x,
  nth n l = x ->
  n < length l ->
  mem x l.
Proof using. introv E N. forwards~ H: Nth_of_nth E. applys* Nth_mem H. Qed.

Lemma nth_app_l : forall n l1 l2,
  n < length l1 ->
  nth n (l1 ++ l2) = nth n l1.
Proof using.
  introv N. applys nth_of_Nth. applys Nth_app_l. applys~ Nth_nth.
Qed.

Lemma nth_app_r : forall n l1 l2,
  n >= length l1 -> 
  nth n (l1 ++ l2) = nth (n - length l1) l2.
Proof using.
  (* -- TODO: investigate issue with Qed if not unfolding nth *) 
  unfold nth. intros n l1. gen n. induction l1; introv N; rew_list in *.
  { fequals; math. }
  { destruct n as [|n']. { false; math. }
    unfold nth_default; fold nth_default. simpl.
    (* rewrite nth_succ. *) rewrite IHl1; [|math].
    fequals; math. }
Qed.

Lemma nth_last_case : forall n x l,
  nth n (l&x) = (If n = length l then x else nth n l).
Proof using.
  intros. case_if.
  { rewrite nth_app_r; [|math]. math_rewrite (n-length l = 0).
    rewrite~ nth_zero. }
  { tests C': (n < length l).
    { rewrite~ nth_app_l. }
    { rewrite nth_gt_length; [|rew_list; math]. 
      rewrite nth_gt_length; [|math]. auto. } }
Qed.

End NthFunc.

Arguments nth [A] {IA}.
Opaque nth.

Hint Rewrite nth_zero nth_succ : rew_listx.


(* ---------------------------------------------------------------------- *)
(** ** Rev *)

Definition rev A (l:list A) : list A :=
  fold_left (fun x acc => x::acc) (@nil A) l.

Section Rev.
Variables (A : Type).
Implicit Types x : A.
Implicit Types l : list A.

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
Proof using. intros. rewrite <- app_cons_one_r. rewrite~ rev_app. Qed.

Lemma rev_one : forall x,
  rev (x::nil) = x::nil.
Proof using. intros. rewrite~ rev_cons. Qed.

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
  introv E. forwards E': f_equal (@rev A) (rm E).
  do 2 rewrite~ rev_rev in E'. 
Qed.

Lemma mem_rev : forall l x,
  mem x l -> 
  mem x (rev l).
Proof using.
  introv H. induction H.
  { rewrite rev_cons. apply mem_last_r. }
  { rewrite rev_cons. apply~ mem_last_l. }
Qed.

Lemma mem_rev_eq : forall l x,
  mem x (rev l) = mem x l.
Proof using.
  extens. iff M.
  { lets H: mem_rev M. rewrite~ rev_rev in H. }
  { apply* mem_rev. }
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

(* TODO: Nth_rev and nth_rev *)

End Rev.

Opaque rev.

Hint Rewrite rev_nil rev_app rev_cons rev_last rev_rev length_rev : rew_list.
Hint Rewrite rev_nil rev_app rev_cons rev_last rev_rev length_rev : rew_listx.
(* Note: [fold_right_rev] may be safely added to [rew_list] *)


(* ---------------------------------------------------------------------- *)
(** ** Inversion for rev *)

Section RevInversion.
Variables (A : Type).
Implicit Types l : list A.

Lemma rev_eq_nil_inv : forall l,
  rev l = nil -> 
  l = nil.
Proof using.
  intros l. destruct l; rew_list; intros.
  { auto. } { false* last_eq_nil_inv. }
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
  intros. lets H1 H2: app_eq_nil_inv H.
  applys_to H2 rev_eq_nil_inv. autos*.
Qed.

(* symmetric of previous lemma *)
Lemma nil_eq_app_rev_inv : forall l1 l2,
  nil = l1 ++ rev l2 -> 
  l1 = nil /\ l2 = nil.
Proof using. intros. apply* app_rev_eq_nil_inv. Qed.

End RevInversion.

Arguments rev_eq_nil_inv [A] [l].
Arguments nil_eq_rev_inv [A] [l].
Arguments app_rev_eq_nil_inv [A] [l1] [l2].
Arguments nil_eq_app_rev_inv [A] [l1] [l2].


(* ---------------------------------------------------------------------- *)
(** * Make *)

Fixpoint make A (n:nat) (v:A) : list A :=
   match n with
   | 0 => nil
   | S n' => v :: make n' v
   end.

Section Make.
Context (A:Type) {IA:Inhab A}.
Implicit Types i n : nat.
Implicit Types v : A.
Implicit Types l : list A.

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
  { math. }
  { rewrite make_succ. fequals_rec. math. }
Qed.

Lemma length_make : forall n v,
  length (make n v) = n.
Proof using.
  intros. induction n.
  { auto. }
  { rewrite make_succ. rewrite length_cons. math. }
Qed.

Lemma Nth_make : forall i n v,
  i < n -> 
  Nth i (make n v) v.
Proof using.
  Hint Constructors Nth.
  introv. gen n; induction i; introv E; destruct n; try solve [ false; math ].
  { constructors. }
  { rewrite make_succ. applys Nth_succ. applys~ IHi. math. }
Qed.

Lemma nth_make : forall i n v,
  i < n -> 
  nth i (make n v) = v.
Proof using. intros. applys nth_of_Nth. applys~ Nth_make. Qed.

End Make.

Opaque make.


(* ---------------------------------------------------------------------- *)
(** * Update as a function *)

Fixpoint update A (n:nat) (v:A) (l:list A) { struct l } : list A :=
  match l with
  | nil => nil
  | x::l' =>
     match n with
     | 0 => v::l'
     | S n' => x::update n' v l'
     end
  end.

Section Update.
Context (A:Type) {IA: Inhab A}.
Implicit Types n : nat.
Implicit Types x v : A.
Implicit Types l : list A.

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

Lemma update_app_l : forall l1 l2 n v,
  n < length l1 ->
  update n v (l1 ++ l2) = update n v l1 ++ l2.
Proof using IA.
  intros l1. induction l1 as [| x l1' ]; introv E; rew_list in *.
  { fequals. math. }
  { destruct n as [|n'].
    { do 2 rewrite update_zero. rew_list~. } 
    { do 2 rewrite update_cons. rew_list~.
      fequals. erewrite* IHl1'. math. } }
Qed.

Lemma update_app_r : forall l1 l2 n v,
  n >= length l1 ->
  update n v (l1 ++ l2) = l1 ++ update (n - length l1) v l2.
Proof using IA.
  intros l1. induction l1 as [| x l1' ]; introv E; rew_list in *.
  { fequals. math. }
  { destruct n as [|n']. { false. math. }
    { rewrite update_cons. fequals. erewrite* IHl1'. math. } }
Qed.

Lemma update_prefix_length : forall l1 l2 x v,
  update (length l1) v (l1 ++ x :: l2) = l1 & v ++ l2.
Proof using IA.
  intros. rew_list. rewrites update_app_r.
  { math_rewrite (length l1 - length l1 = 0). rew_list~. }
  { math. }
Qed.

Lemma update_ge_length : forall n v l,
  n >= length l ->
  update n v l = l.
Proof using.
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

Lemma nth_update_same : forall n l v,
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
  n <> m ->
  nth n (update m v l) = nth n l.
Proof using.
  intros n m l. gen n m. induction l; introv N.
  { rewrite~ update_nil. }
  { destruct m as [|m'].
    { rewrite update_zero. do 2 (rewrite nth_pos; [|math]). auto. }
    { rewrite update_succ. destruct n as [|n'].
      { rew_listx~. }
      { rew_listx. applys~ IHl. } } }
Qed.

(* TODO: possibly add Nth_update_eq and Nth_update_neq *)

End Update.

Opaque update.


(* ---------------------------------------------------------------------- *)
(** ** Map *)

Definition map A B (f:A->B) (l:list A) : list B :=
  fold_right (fun x acc => (f x)::acc) (@nil B) l.

Section Map.
Variable (A B : Type).
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types f : A -> B.

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

Lemma mem_map : forall (A B:Type) (f:A->B) (l:list A) x,
  mem x l -> 
  mem (f x) (map f l).
Proof using. introv M. induction M; rew_listx; auto. Qed.

Lemma Nth_map : forall (A B:Type) (f:A->B) (l:list A) n (x:A),
  Nth n l x -> 
  Nth n (map f l) (f x).
Proof using.
  Hint Constructors Nth.
  introv M. induction M; rew_listx; auto.
Qed.

Lemma nth_map : forall `{IA:Inhab A} `{IB:Inhab B} (f:A->B) (l:list A) n,
  n < length l -> 
  nth n (map f l) = f (nth n l).
Proof using.
  introv N. applys nth_of_Nth. applys Nth_map. applys~ Nth_of_nth.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Concat *)

Definition concat A (m:list (list A)) : list A :=
  fold_right (@app A) (@nil A) m.

Section Concat.
Variables (A : Type).
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types m : list (list A).

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

Lemma mem_concat_eq : forall m x,
    mem x (concat m)
  = exists l, mem l m /\ mem x l.
Proof using.
  Hint Constructors mem.
  introv. extens. induction m.
  { simpl. iff I. { inverts I. } { destruct I as (?&H&?). inverts H. } }
  { rewrite concat_cons. rewrite mem_app_eq. iff I (l&M&N).
    { destruct I as [I|I].
      { exists~ a. }
      { rewrite IHm in I. destruct* I as (l&?&?). } }
    { inverts* M. } }
Qed.

Lemma concat_eq_nil_mem_inv : forall l m,
  concat m = nil ->
  mem l m ->
  l = nil.
Proof using.
  introv E M. induction M as [|x].
  { rewrite concat_cons in E. forwards*: app_eq_nil_inv E. }
  { rewrite concat_cons in E. destruct x. 
    { rew_list in E. applys~ IHM. }
    { rew_list in E. false. } }
Qed.

(* TODO: possibly add length_concat and nth_concat *)

End Concat.

Opaque concat.

Hint Rewrite concat_nil concat_cons concat_app concat_last : rew_listx.


(* ---------------------------------------------------------------------- *)
(** ** Filter *)

(** [filter P l] produces a list [l'] that is the sublist of [l]
    made exactly of the elements of [l] that satisfy [P]. *)

Definition filter A (P:A->Prop) l :=
  fold_right (fun x acc => If P x then x::acc else acc) (@nil A) l.

Section Filter.
Variables (A : Type).
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types P : A -> Prop.
Hint Constructors mem.

Lemma filter_nil : forall P,
  filter P nil = nil.
Proof using. auto. Qed.

Lemma filter_cons : forall x l P,
  filter P (x::l) = (If P x then x :: filter P l else filter P l).
Proof using. auto. Qed.

Lemma filter_app : forall l1 l2 P,
  filter P (l1 ++ l2) = filter P l1 ++ filter P l2.
Proof using. (* todo: factorise with map_app and above *)
  intros. unfold filter.
  assert (forall accu,
    fold_right (fun x acc => If P x then x::acc else acc) accu (l1 ++ l2) =
    fold_right (fun x acc => If P x then x::acc else acc) nil l1 ++
     fold_right (fun x acc => If P x then x::acc else acc) nil l2 ++ accu).
  { induction l1; intros.
    { rew_list. gen accu. induction l2; intros.
      { auto. }
      { rew_listx. case_if. rew_list. fequals. rewrite IHl2. fequals. } }
    { rew_listx. case_if. rew_list. fequals. rewrite IHl1. fequals. } }
  specializes H (@nil A). rewrite~ app_nil_r in H.
Qed.

Lemma filter_last : forall x l P,
  filter P (l & x) = filter P l ++ (If P x then x::nil else nil).
Proof using. intros. rewrite~ filter_app. Qed.

Lemma mem_filter_eq : forall x P l,
  mem x (filter P l) = (mem x l /\ P x).
Proof using.
  intros. extens. induction l.
  { rewrite filter_nil. iff M (M&?); inverts M. }
  { rewrite filter_cons. case_if; rew_listx; rewrite IHl.
    { iff [M|M] N; subst*. }
    { iff M ([N|N]&K); subst*. } }
Qed.

Lemma mem_filter : forall x P l,
  mem x l -> 
  P x -> 
  mem x (filter P l).
Proof using. intros. rewrite* mem_filter_eq. Qed.

Lemma mem_filter_inv : forall x P l,
  mem x (filter P l) -> 
  mem x l /\ P x.
Proof using. introv E. rewrite* mem_filter_eq in E. Qed.

Lemma length_filter : forall l P,
  length (filter P l) <= length l.
Proof using.
  intros. induction l.
  { rewrite filter_nil. math. }
  { rewrite filter_cons. case_if; rew_list; math. }
Qed.

Lemma filter_length_two_disjoint : forall (P Q : A-> Prop) l,
  (forall x, mem x l -> P x -> Q x -> False) ->
  length (filter P l) + length (filter Q l) <= length l.
Proof using.
  introv. induction l; introv H.
  { rew_list. nat_math. }
  { specializes IHl. { intros. applys* H x. }
    repeat rewrite filter_cons. do 2 case_if; rew_list.
    { false* H. } { nat_math. } { nat_math. } { nat_math. } }
Qed.

Lemma filter_length_partition : forall P l,
    length (filter (fun x => P x) l) 
  + length (filter (fun x => ~ P x) l) 
  <= length l.
Proof using.
  intros. applys~ filter_length_two_disjoint P (fun x => ~ P x) l.
Qed.

Lemma length_filter_eq_mem_ge_one : forall x l,
  mem x l ->
  length (filter (= x) l) >= 1.
Proof using.
  introv M. induction l.
  { inverts M. }
  { rewrite filter_cons. case_if.
    { rew_list. nat_math. }
    { inverts M. false. applys~ IHl. } }
Qed.

(* TODO: filter_congruence: filter prodides equal
    results for predicate equivalent on all elements in l. *)

End Filter.

Opaque filter.

Hint Rewrite filter_nil filter_cons filter_app filter_last
             mem_filter_eq : rew_listx.


(* ---------------------------------------------------------------------- *)
(** ** Remove *)

Definition remove A (a:A) (l:list A) :=
  filter (<> a) l.

Section Remove.
Variables (A : Type).
Implicit Types a x : A.
Implicit Types l : list A.

Lemma remove_as_filter : forall a l,
  remove a l = filter (<> a) l.
Proof using. auto. Qed.

Lemma mem_remove_eq : forall x a l,
  mem x (remove a l) = (mem x l /\ x <> a).
Proof using. intros. applys* mem_filter_eq. Qed.

Lemma mem_remove : forall a x l,
  mem x l -> 
  x <> a -> 
  mem x (remove a l).
Proof using. intros. rewrite* mem_remove_eq. Qed.

Lemma mem_remove_inv : forall x a l,
  mem x (remove a l) -> 
  mem x l /\ x <> a.
Proof using. introv E. rewrite* mem_remove_eq in E. Qed.

Lemma mem_remove_same_inv : forall x l,
  mem x (remove x l) ->
  False.
Proof using. introv E. lets: mem_remove_inv E. false*. Qed.

Lemma length_remove : forall l a,
  length (remove a l) <= length l.
Proof using. intros. applys length_filter. Qed.

Lemma length_remove_mem : forall x l,
  mem x l -> 
  length (remove x l) < length l.
Proof using.
  unfold remove. intros x l. induction l; rew_listx; introv M.
  { false. }
  { case_if; rew_list.
    { destruct M; tryfalse. forwards~: IHl. math. }
    { lets: length_filter l (<> x). math. } }
Qed.

(* LATER: lemma for [remove x (remove y) l = ...] *)

End Remove.

Opaque remove.


(* ---------------------------------------------------------------------- *)
(* ** Noduplicates *)

(** [noduplicates L] asserts that [L] does not contain any
    duplicated item. *)

Inductive noduplicates A : list A -> Prop :=
  | noduplicates_nil : noduplicates nil
  | noduplicates_cons : forall x l,
      ~ (mem x l) -> 
      noduplicates l -> 
      noduplicates (x::l).

Section Noduplicates.
Variables (A : Type).
Implicit Types l : list A.
Hint Constructors noduplicates.

Lemma noduplicates_one : forall (x:A),
  noduplicates (x::nil).
Proof using.
  intros. applys noduplicates_cons. { intros M. false* mem_nil_inv. }
  applys noduplicates_nil.
Qed.

Lemma noduplicates_two : forall (x y:A),
  x <> y ->
  noduplicates (x::y::nil).
Proof using.
  intros. applys noduplicates_cons.
  { intros M. rewrite mem_one_eq in M. false. }
  applys noduplicates_one.
Qed.

Lemma noduplicates_app : forall l1 l2,
  noduplicates l1 ->
  noduplicates l2 ->
  (forall x, mem x l1 -> mem x l2 -> False) ->
  noduplicates (l1 ++ l2).
Proof using.
  Hint Constructors mem.
  intros l1. induction l1; introv N1 N2 EQ; rew_list.
  { auto. }
  { inverts N1 as N N1'. constructors.
    { rewrite mem_app_eq. rew_logic*. }
    { applys~ IHl1. introv Mx1 Mx2. applys* EQ x. } }
Qed.

Lemma noduplicates_app_inv : forall l1 l2,
  noduplicates (l1 ++ l2) ->
     noduplicates l1
  /\ noduplicates l2 
  /\ ~ (exists x, mem x l1 /\ mem x l2).
Proof using.
  introv ND. splits.
  { induction l1.
    { constructors. }
    { rew_list in ND. inverts ND as ND1 ND2.
      rewrite mem_app_eq in ND1. rew_logic* in ND1. } }
  { induction l1; rew_list in ND.
    { auto. }
    { inverts~ ND. } }
  { introv (x&I1&I2). induction I1; rew_list in ND.
    { inverts ND as ND1 ND2. false ND1. apply* mem_app. }
    { apply IHI1. inverts~ ND. } }
Qed.

Lemma noduplicates_length_le : forall l1 l2,
  noduplicates l1 ->
  (forall x, mem x l1 -> mem x l2) ->
  length l1 <= length l2.
Proof using.
  Hint Constructors mem.
  introv NL ML. gen l2. induction l1 as [|a l1']; intros; rew_list.
  { math. }
  { inverts NL as HM NL'. sets_eq l2': (remove a l2).
   forwards H: length_remove_mem a l2. { applys* ML. }
   rewrite <- EQl2' in H.
   forwards~: IHl1' l2'. 
   { introv N. tests: (x = a). subst l2'. applys* mem_remove. }
   math. }
Qed.

Lemma noduplicates_length_eq : forall l1 l2,
  noduplicates l1 ->
  noduplicates l2 ->
  (forall x, mem x l1 <-> mem x l2) ->
  length l1 = length l2.
Proof using.
  introv H1 H2 EQ.
  forwards~: noduplicates_length_le l1 l2. { intros. rewrite~ <- EQ. }
  forwards~: noduplicates_length_le l2 l1. { intros. rewrite~ EQ. }
  math.
Qed.

Lemma noduplicates_Nth_same  : forall l,
  (forall n1 n2 x,
     Nth n1 l x ->
     Nth n2 l x ->
     n1 = n2) ->
  noduplicates l.
Proof using.
  introv NL. induction l; constructors.
  { introv I. lets (n&N): mem_Nth (rm I).
    forwards* Ab: NL Nth_zero Nth_succ. inverts Ab. }
  { apply IHl. introv N1 N2. forwards G: NL.
    applys Nth_succ N1. applys Nth_succ N2. inverts~ G. }
Qed.

Lemma noduplicates_Nth_same_inv : forall l n1 n2 x,
  noduplicates l ->
  Nth n1 l x ->
  Nth n2 l x ->
  n1 = n2.
Proof using.
  introv NL. gen n1 n2. induction NL; introv N1 N2.
  { inverts N1. }
  { inverts N1 as N1; inverts N2 as N2; autos~.
    { apply Nth_mem in N2. false*. }
    { apply Nth_mem in N1. false*. } }
Qed.

Lemma noduplicates_filter : forall P l,
  noduplicates l -> 
  noduplicates (filter P l).
Proof using.
  introv H. induction H; rew_listx. { auto. }
  { case_if.
    { constructors*. rew_listx*. }
    { auto. } }
Qed.

Lemma noduplicates_remove : forall a l,
  noduplicates l -> 
  noduplicates (remove a l).
Proof using.
  intros. rewrite remove_as_filter. applys* noduplicates_filter.
Qed.

(* TODO: noduplicates_rev *)

End Noduplicates.


(* ---------------------------------------------------------------------- *)
(* ** remove_duplicates *)

(** [remove_duplicates l] produces a list [l'] that is the sublist of [l]
    obtained by keeping only the first occurence of every item. *)

Fixpoint remove_duplicates A (l:list A) :=
  match l with
  | nil => nil
  | x::l' => x :: (remove x (remove_duplicates l'))
  end.

Section Remove_duplicates.
Variables (A : Type).
Implicit Types l : list A.
Hint Constructors mem noduplicates.

Lemma remove_duplicates_spec : forall l l',
  l' = remove_duplicates l ->
     noduplicates l'
  /\ (forall x, mem x l' <-> mem x l)
  /\ length l' <= length l.
Proof using.
  introv E.
  asserts (R1&R2): (noduplicates l' /\ (forall x, mem x l' <-> mem x l)).
  { gen l' E. induction l; introv E; simpls.
    { subst. splits*. } 
    { sets_eq l'': (remove_duplicates l). forwards~ [E' M]: IHl. subst l'. splits.
      { constructors. applys~ mem_remove_same_inv. applys~ noduplicates_remove. }
      { intros x. lets (M1&M2): M x. iff N.
        { inverts N as R. auto. lets: mem_remove_inv R. constructors*. }
        { lets [E|(H1&H2)]: mem_cons_inv_cases N. { subst*. }
          constructors. applys* mem_remove. } } } }
  splits~. applys~ noduplicates_length_le. introv Hx. rewrite~ <- R2.
Qed.

Lemma noduplicates_remove_duplicates : forall l,
  noduplicates (remove_duplicates l).
Proof using. introv. forwards*: remove_duplicates_spec l. Qed.

Lemma mem_remove_duplicates : forall x l,
  mem x (remove_duplicates l) = mem x l.
Proof using. 
  introv. extens. repeat rewrite <- Mem_mem. apply~ remove_duplicates_spec. 
Qed.

Lemma length_remove_duplicates : forall l,
  length (remove_duplicates l) <= length l.
Proof using. introv. forwards*: remove_duplicates_spec l. Qed.

End Remove_duplicates.

Hint Rewrite mem_remove_duplicates : rew_listx.


(* ---------------------------------------------------------------------- *)
(** ** Combine *)

Fixpoint combine A B (r:list A) (s:list B) : list (A*B) :=
  match r with
  | nil => nil
  | a::r' =>
    match s with
    | nil => arbitrary
    | b::s' => (a,b)::(combine r' s')
    end
  end.

Section Combine.
Variable (A B : Type).
Implicit Types r : list A.
Implicit Types s : list B.

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

Lemma Nth_combine : forall A B n (r:list A) (s:list B) x y,
  Nth n r x ->
  Nth n s y ->
  Nth n (combine r s) (x,y).
Proof using. 
  introv N1. gen s. induction N1; introv N2; inverts N2.
  { constructors. }
  { rewrite combine_cons. constructors~. }
Qed.

Lemma nth_combine : forall `{IA:Inhab A} `{IB:Inhab B} n (r:list A) (s:list B),
  n < length r ->
  length r = length s ->
  nth n (combine r s) = (nth n r, nth n s).
Proof using. 
  introv N E. applys nth_of_Nth. applys* Nth_combine.
  { applys* Nth_nth. } { applys* Nth_nth. math. }
Qed.

Opaque combine.

Hint Rewrite combine_nil combine_cons : rew_listx.


(* ---------------------------------------------------------------------- *)
(** ** Split *)

Fixpoint split A B (l:list(A*B)) : (list A * list B) :=
  match l with
  | nil => (nil,nil)
  | (a,b)::l' => let (la,lb) := split l' in (a::la, b::lb)
  end.

Section Split.
Variable (A B : Type).
Implicit Types l : list (A*B).
Implicit Types x : A.
Implicit Types y : B.
Implicit Types r : list A.
Implicit Types s : list B.

Lemma split_nil : 
  split (@nil (A*B)) = (nil, nil).
Proof using. auto. Qed.

Lemma split_cons_let : forall x y l,
  split ((x,y)::l) = let '(r,s) := split l in (x::r, y::s).
Proof using. auto. Qed.

Lemma split_cons : forall x y l r s,
  (r,s) = split l ->
  split ((x,y)::l) = (x::r, y::s).
Proof using.
  introv H. rewrite split_cons_let. rewrite~ <- H.
Qed.

Lemma split_app : forall l1 l2 r1 r2 s1 s2,
  (r1,s1) = split l1 ->
  (r2,s2) = split l2 ->
  split (l1++l2) = (r1++r2, s1++s2).
Proof using.
  intros l1. induction l1 as [|[x y] l1']; introv H1 H2.
  { rewrite split_nil in H1. inverts~ H1. }
  { rewrite split_cons_let in H1. destruct (split l1') as [r1' s1'].
    inverts H1. rew_list. rewrite split_cons_let. 
    erewrite~ (IHl1' l2). }
Qed.

Lemma split_last : forall x y l r s,
  (r,s) = split l ->
  split (l&(x,y)) = (r&x, s&y).
Proof using. introv H. erewrite split_app; fequals. Qed.

Lemma split_length : forall l r s,
  (r,s) = split l ->
  length r = length l /\ length s = length l.
Proof using. 
  intros l. induction l as [|[x y] l']; introv E.
  { rewrite split_nil in E. inverts~ E. } 
  { rewrite split_cons_let in E. destruct (split l') as [r' s'].
    inverts E. rew_list. forwards~ (?&?): IHl'. }
Qed.

Lemma split_length_l : forall l r s,
  (r,s) = split l ->
  length r = length l.
Proof using. introv E. forwards*: split_length E. Qed.

Lemma split_length_r : forall l r s,
  (r,s) = split l ->
  length s = length l.
Proof using. introv E. forwards*: split_length E. Qed.

Lemma Nth_split : forall n l x y r s,
  Nth n l (x,y) ->
  (r,s) = split l ->
  Nth n r x /\ Nth n s y.
Proof using.
  Hint Constructors Nth.
  introv N E. gen_eq p: (x,y). gen r s x y. 
  induction N as [l' [x' y']|[x' y'] n' l' [x'' y'']]; intros.
  { inverts EQp. rewrite split_cons_let in E.
    destruct (split l') as [r' s']. inverts* E. }
  { inverts EQp. rewrite split_cons_let in E.
    destruct (split l') as [r' s'].
    forwards*: IHN. inverts* E. }
Qed.

(* TODO: discuss whether Nth_split_r and Nth_split_l are needed *)

Lemma nth_split : forall `{IA:Inhab A} `{IB:Inhab B} n l (r:list A) (s:list B),
  (r,s) = split l ->
  n < length l ->
  nth n l = (nth n r, nth n s).
Proof using. 
  introv E N. applys nth_of_Nth. lets ([x y]&M): Nth_inbound_inv N.
  forwards (F1&F2): Nth_split M E.
  rewrite (nth_of_Nth F1). rewrite~ (nth_of_Nth F2).
Qed.

Lemma nth_split_l : forall `{IA:Inhab A} `{IB:Inhab B} n l (r:list A) (s:list B),
  (r,s) = split l ->
  n < length l ->
  nth n r = fst (nth n l).
Proof using. introv E N. rewrites~ (>> nth_split E N). Qed.

Lemma nth_split_r : forall `{IA:Inhab A} `{IB:Inhab B} n l (r:list A) (s:list B),
  (r,s) = split l ->
  n < length l ->
  nth n s = snd (nth n l).
Proof using. introv E N. rewrites~ (>> nth_split E N). Qed.

End Split.

Opaque split.

Hint Rewrite split_nil : rew_listx.


(* ---------------------------------------------------------------------- *)
(** ** Take *)

Fixpoint take A (n:nat) (l:list A) : list A :=
  match n with
  | 0 => nil
  | S n' => match l with
    | nil => nil
    | a::l' => a::(take n' l')
    end
  end.

Section Take.
Variables (A : Type).
Implicit Types n : nat.
Implicit Types x : A.
Implicit Types l : list A.

Lemma take_nil : forall n,
  take n (@nil A) = nil.
Proof using. intros. destruct n; auto. Qed.

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

Lemma take_is_prefix : forall n l,
  exists q, l = take n l ++ q.
Proof using.
  intros n l. gen n. induction l; intros.
  { exists (@nil A). rewrite~ take_nil. }
  { destruct n as [|n']. 
    { rewrite take_zero. exists~ (a::l). }
    { rewrite take_succ. forwards (q'&E): IHl n'. exists q'.
      rew_list. congruence. } }
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

(* See below for [length_take] and other properties *)

End Take.

(* Arguments take [A] : simpl never. *)
Opaque take.

Hint Rewrite take_nil take_zero take_succ : rew_listx.
(* Note: [take_prefix_length] and [take_full_length] 
   may be safely added to [rew_listx]. *)


(* ---------------------------------------------------------------------- *)
(** ** Drop *)

Fixpoint drop A (n:nat) (l:list A) : list A :=
  match n with
  | 0 => l
  | S n' => match l with
    | nil => nil
    | a::l' => drop n' l'
    end
  end.

Section Drop.
Variables (A : Type).
Implicit Types n : nat.
Implicit Types x : A.
Implicit Types l : list A.

Lemma drop_nil : forall n,
  drop n (@nil A) = nil.
Proof using. intros. destruct n; auto. Qed.

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

Lemma drop_is_suffix : forall n l,
  exists q, l = q ++ drop n l.
Proof using.
  intros n l. gen n. induction l; intros.
  { exists (@nil A). rewrite~ drop_nil. }
  { destruct n as [|n']. 
    { rewrite drop_zero. exists~ (@nil A). }
    { rewrite drop_succ. forwards (q'&E): IHl n'. exists (a::q').
      rew_list. congruence. } }
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

(* See below for [length_drop] and other properties *)

End Drop.

Opaque drop.
(* Arguments drop [A] : simpl never. *)

Hint Rewrite drop_nil drop_zero drop_succ : rew_listx.
(* Note: [drop_prefix_length] and [drop_full_length] 
   may be safely added to [rew_list]. *)


(* ---------------------------------------------------------------------- *)
(** ** Take and drop decomposition of a list *)

Section TakeAndDrop.
Variables (A : Type).
Implicit Types x : A.
Implicit Types l : list A.

Lemma take_app_drop_spec : forall n l f r,
  f = take n l -> 
  r = drop n l -> 
  n <= length l ->
     l = f ++ r 
  /\ length f = n
  /\ length r = length l - n.
Proof using.
  intros n. induction n; introv F R L.
  { subst. rew_listx. splits~. math. }
  { destruct l; rew_listx in L.
    { rew_listx in L. false. math. }
    { forwards~ (F'&R'&L'): (>> IHn l (take n l) r). { math. }
      subst f. rew_listx. splits. { fequals. } { math. } { math. } } }
Qed.

Lemma take_spec : forall n l,
  n <= length l ->
  exists l', length (take n l) = n
          /\ l = (take n l) ++ l'.
Proof using. introv E. forwards* (E1&E2&E3): take_app_drop_spec. Qed.

Lemma length_take : forall n l,
  n <= length l ->
  length (take n l) = n.
Proof using. introv E. forwards~ (l'&N&M): take_spec n l. Qed.

Lemma drop_spec : forall n l,
  n <= length l ->
  exists l', length l' = n 
          /\ l = l' ++ (drop n l).
Proof using. introv E. forwards* (E1&E2&E3): take_app_drop_spec. Qed.

Lemma length_drop : forall n l,
  n <= length l ->
  length (drop n l) = length l - n.
Proof using.
  introv E. forwards~ (l'&N&M): drop_spec n l.
  pattern l at 2. rewrite M. rew_list. math.
Qed.

(* TODO: Nth_take_l, etc... 

  Lemma Nth_take_l : forall n m l l' x, 
    n < m ->
    Nth n l x ->
    Nth n (take m l) x.

  Lemma Nth_take_inv : forall n m l l' x, 
    Nth n (take m l) x ->
    n < m /\ Nth n l x.

*)

End TakeAndDrop.

Arguments take_app_drop_spec [A].
Arguments take_spec [A].
Arguments drop_spec [A].


(* ---------------------------------------------------------------------- *)
(** ** TakeDropLast *)

(** [take_drop_last l] returns a pair [(q,x)] such that
    [l = q & x] *)

Fixpoint take_drop_last `{IA:Inhab A} (l:list A) : (list A)*A :=
  match l with
  | nil => arbitrary
  | x::l' =>
    match l' with
    | nil => (nil,x)
    | _ => let (t,y) := take_drop_last l' in
           (x::t, y)
    end
  end.

Section TakeDropLast.
Context (A:Type) {IA:Inhab A}.
Implicit Types x : A.
Implicit Types l : list A.

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

(* TODO: more properties of take_drop_last *)
(* TODO: find a better name for this function *)

End TakeDropLast.

Opaque take_drop_last.
Arguments take_drop_last [A] {IA}.
Arguments take_drop_last_spec [A] {IA}.
Arguments take_drop_last_length [A] {IA}.


(* ---------------------------------------------------------------------- *)
(* ** Forall *)

(** [Forall P l] asserts that all the elements in the list [l]
    satisfy the predicate [P]. *)

Inductive Forall A (P:A->Prop) : list A -> Prop :=
  | Forall_nil :
      Forall P nil
  | Forall_cons : forall l x,
      P x -> 
      Forall P l ->
      Forall P (x::l).

Section ForallProp.
Variables A : Type.
Implicit Types l : list A.
Implicit Types P : A->Prop.
Hint Constructors Forall.

(* Rewriting *)

Lemma Forall_nil_eq : forall P,
  Forall P nil = True.
Proof using. auto. Qed.

Lemma Forall_cons_eq : forall P l x,
  Forall P (x::l) = (P x /\ Forall P l).
Proof using.
  intros. extens. iff M. { inverts* M. } { constructors*. }
Qed.

Lemma Forall_one_eq : forall P x,
  Forall P (x::nil) = (P x).
Proof using.
  intros. extens. rewrite Forall_cons_eq. rewrite* Forall_nil_eq. 
Qed.

Lemma Forall_app_eq : forall P l1 l2,
  Forall P (l1 ++ l2) = (Forall P l1 /\ Forall P l2).
Proof using.
  intros. extens. induction l1; rew_list.
  { autos*. }
  { iff M (M1&M2). { inverts* M. } { inverts* M1. } }
Qed.

Lemma Forall_last_eq : forall P l x,
  Forall P (l & x) = (Forall P l /\ P x).
Proof using.
  intros. extens. induction l; rew_list.
  { iff M (M1&M2). { inverts* M. } { autos*. } }
  { iff M (M1&M2). { inverts* M. } { inverts* M1. } }
Qed.

(* Constructors *)

Lemma Forall_app : forall P l1 l2,
  Forall P l1 -> 
  Forall P l2 ->
  Forall P (l1 ++ l2).
Proof using. intros. rewrite* Forall_app_eq. Qed.

Lemma Forall_last : forall P l x,
  Forall P l -> 
  P x ->
  Forall P (l & x).
Proof using. intros. rewrite* Forall_last_eq. Qed.

(* Inversion *)

Lemma Forall_cons_inv : forall P l x,
  Forall P (x::l) ->
  P x /\ Forall P l.
Proof using. introv H. rewrite* Forall_cons_eq in H. Qed.

Lemma Forall_cons_inv_head : forall P l x,
  Forall P (x::l) ->
  P x.
Proof using. introv H. rewrite* Forall_cons_eq in H. Qed.

Lemma Forall_cons_inv_tail : forall P l x,
  Forall P (x::l) ->
  Forall P l.
Proof using. introv H. rewrite* Forall_cons_eq in H. Qed.

Lemma Forall_app_inv : forall P l1 l2,
  Forall P (l1 ++ l2) ->
  Forall P l1 /\ Forall P l2.
Proof using. introv H. rewrite* Forall_app_eq in H. Qed.

Lemma Forall_last_inv : forall P l x,
  Forall P (l & x) ->
  Forall P l /\ P x.
Proof using. introv H. rewrite* Forall_last_eq in H. Qed.

(* Others *)

Lemma Forall_eq_forall_mem : forall P l,
  Forall P l = (forall x, mem x l -> P x).
Proof using.
  extens. introv. induction l; iff I.
  { introv IN. inverts IN. }
  { auto. }
  { introv IN. rew_listx in IN. inverts I. destruct IN; subst*. }
  { constructors.
    { apply I. rew_listx*. }
    { apply~ IHl. introv IN. apply~ I. rew_listx*. } }
Qed.

Lemma Forall_mem_inv : forall P l x,
  Forall P l ->
  mem x l ->
  P x.
Proof using. introv F I. rewrite Forall_eq_forall_mem in F. apply~ F. Qed.

Lemma Forall_Nth_inv : forall P n l x,
  Forall P l ->
  Nth n l x ->
  P x.
Proof using. introv F N. applys* Forall_mem_inv F. applys* Nth_mem. Qed.

Lemma Forall_nth_inv : forall {IA:Inhab A} P n l,
  Forall P l ->
  n < length l ->
  P (nth n l).
Proof using. introv F N. applys Forall_Nth_inv n F. applys~ Nth_nth. Qed.

Lemma Forall_rev : forall P l,
  Forall P l ->
  Forall P (rev l).
Proof using.
  introv E. induction l.
  { auto. }
  { rew_list. rewrite Forall_last_eq. inverts* E. }
Qed.

Lemma Forall_rev_eq : forall P l,
  Forall P (rev l) = Forall P l.
Proof using.
  intros. extens. iff M.
  { rewrite <- rev_rev. applys~ Forall_rev. }
  { applys~ Forall_rev. }
Qed.

Lemma Forall_take : forall P n l,
  Forall P l ->
  Forall P (take n l).
Proof using.
  introv E. forwards (q&K): take_is_prefix n l. 
  rewrite K in E. rewrite* Forall_app_eq in E.
Qed.

Lemma Forall_drop : forall P n l,
  Forall P l ->
  Forall P (drop n l).
Proof using.
  introv E. forwards (q&K): drop_is_suffix n l. 
  rewrite K in E. rewrite* Forall_app_eq in E.
Qed.

Lemma Forall_pred_incl : forall P Q l,
  Forall P l -> 
  pred_incl P Q ->
  Forall Q l.
Proof using. introv. induction l; introv H L; inverts* H. Qed.

Lemma Forall_filter_same : forall P l,
  Forall P (filter P l).
Proof using.
  introv. induction l.
  { rewrite filter_nil. constructors~. }
  { rewrite filter_cons. cases_if~. }
Qed.

Lemma Forall_filter_pred_incl : forall P Q l,
  pred_incl P Q ->
  Forall Q (filter P l).
Proof using.
  introv E. applys~ Forall_pred_incl P. applys Forall_filter_same.
Qed.

End ForallProp.

Hint Rewrite Forall_nil_eq Forall_cons_eq Forall_app_eq Forall_last_eq
  Forall_rev_eq : rew_listx.


(* ---------------------------------------------------------------------- *)
(* ** Forall2 *)

(** [Forall2 P L1 L2] asserts that the lists [L1] and [L2]
    have the same length and that elements at corresponding
    indices are related by the binary relation [P]. *)

Inductive Forall2 A B (P:A->B->Prop) : list A -> list B -> Prop :=
  | Forall2_nil :
      Forall2 P nil nil
  | Forall2_cons : forall s r x y,
      P x y -> 
      Forall2 P s r ->
      Forall2 P (x::s) (y::r).

Section Forall2.
Variables A B : Type.
Implicit Types x : A.
Implicit Types y : B.
Implicit Types r : list A.
Implicit Types s : list B.
Implicit Types P : A -> B -> Prop.
Hint Constructors Forall2.

(* Basic *)

Lemma Forall2_inv_length : forall P r s,
  Forall2 P r s -> 
  length r = length s.
Proof using. introv H. induction H; rew_list; math. Qed.

(* Constructors *)

Lemma Forall2_app : forall P r1 s1 r2 s2,
  Forall2 P r1 s1 -> 
  Forall2 P r2 s2 ->
  Forall2 P (r1 ++ r2) (s1 ++ s2).
Proof using. introv H H'. induction H; rew_list~. Qed.

Lemma Forall2_last : forall P r s x y,
  Forall2 P r s -> 
  P x y ->
  Forall2 P (r & x) (s & y).
Proof using. intros. apply~ Forall2_app. Qed.

(* Rewriting *)

Lemma Forall2_nil_eq : forall P,
  Forall2 P nil nil = True.
Proof using. intros. extens. iff M. { inverts* M. } { auto. } Qed.

Lemma Forall2_cons_eq : forall P x y r s,
  Forall2 P (x::r) (y::s) = (P x y /\ Forall2 P r s).
Proof using. intros. extens. iff M (M1&M2). { inverts* M. } { auto. } Qed.

Lemma Forall2_one_eq : forall P x y,
  Forall2 P (x::nil) (y::nil) = P x y.
Proof using. intros. extens. rewrite Forall2_cons_eq. rewrite* Forall2_nil_eq. Qed.

Lemma Forall2_app_eq : forall r1 r2 s1 s2 P,
  length r1 = length s1 ->
  Forall2 P (r1 ++ r2) (s1 ++ s2) = (Forall2 P r1 s1 /\ Forall2 P r2 s2).
Proof using. 
  intros r1. induction r1; introv E; 
    destruct s1; tryfalse; rew_list in *; extens.
  { autos*. }
  { iff M (M1&M2). 
    { inverts M as N1 N2. rewrite* IHr1 in N2. }
    { inverts M1. constructors~. rewrite* IHr1. } }
Qed.

Lemma Forall2_last_eq : forall P r s x y,
  Forall2 P (r & x) (s & y) = (Forall2 P r s /\ P x y).
Proof using.  
  intros. extens. iff M (M1&M2).
  { lets E: Forall2_inv_length M. rew_list in E.
    rewrite~ Forall2_app_eq in M. destruct M as (M1&M2). inverts* M2. }
  { applys~ Forall2_last. }
Qed.

(* Inversion *)

Lemma Forall2_cons_inv : forall P r s x y,
  Forall2 P (x::r) (y::s) ->
  P x y /\ Forall2 P r s.
Proof using. introv E. rewrite~ Forall2_cons_eq in E. Qed.

Lemma Forall2_cons_l_inv : forall P r1 s x,
  Forall2 P (x::r1) s ->
  exists y s1, s = y::s1 /\ P x y /\ Forall2 P r1 s1.
Proof using. introv E. destruct s as [|y s1]; inverts E. autos*. Qed.

Lemma Forall2_cons_r_inv : forall P r s1 y,
  Forall2 P r (y::s1) ->
  exists x r1, r = x::r1 /\ P x y /\ Forall2 P r1 s1.
Proof using. introv E. destruct r as [|x r1]; inverts E. autos*. Qed.

Lemma Forall2_app_inv : forall P r1 s1 r2 s2,
  Forall2 P (r1 ++ r2) (s1 ++ s2) ->
  length r1 = length s1 ->
  Forall2 P r1 s1 /\ Forall2 P r2 s2.
Proof using. introv M E. rewrite~ Forall2_app_eq in M. Qed.

Lemma Forall2_last_inv : forall P r s x y,
  Forall2 P (r & x) (s & y) ->
  Forall2 P r s /\ P x y.
Proof using. introv E. rewrite~ Forall2_last_eq in E. Qed.

Lemma Forall2_last_l_inv : forall P r1 s x,
  Forall2 P (r1 & x) s ->
  exists s1 y, s = s1 & y /\ P x y /\ Forall2 P r1 s1.
Proof using.
  introv M. forwards (y&s1&E): list_neq_nil_inv_last s.
  { intro_subst. inverts M. applys* nil_eq_last_inv. }
  subst s. rewrite* Forall2_last_eq in M.
Qed.

Lemma Forall2_last_r_inv : forall P r s1 y,
  Forall2 P r (s1 & y) ->
  exists r1 x, r = r1 & x /\ P x y /\ Forall2 P r1 s1.
Proof using.
  introv M. forwards (x&r1&E): list_neq_nil_inv_last r.
  { intro_subst. inverts M. applys* nil_eq_last_inv. }
  subst r. rewrite* Forall2_last_eq in M.
Qed.

(* Interactions *)

Lemma Forall2_swap : forall P r s,
  Forall2 P r s ->
  Forall2 (fun b a => P a b) s r.
Proof using. introv F. induction~ F. Qed.

Lemma Forall2_swap_inv : forall P r s,
  Forall2 (fun b a => P a b) s r ->
  Forall2 P r s.
Proof using. introv F. induction~ F. Qed.

Lemma Forall2_swap_eq : forall P r s,
  Forall2 P r s = Forall2 (fun b a => P a b) s r.
Proof using.
  intros. extens. iff M.
  { applys* Forall2_swap. }
  { applys* Forall2_swap_inv. } 
Qed.

Lemma Forall2_rel_le : forall P Q r s,
  Forall2 P r s ->
  rel_incl P Q -> 
  Forall2 Q r s.
Proof using.
  introv F W. unfolds rel_incl, pred_incl. induction F; constructors~.
Qed.

Lemma Forall2_rev : forall P r s,
  Forall2 P r s ->
  Forall2 P (rev r) (rev s).
Proof using.
  Hint Resolve Forall2_last.
  intros P r. induction r; introv M; inverts M; rew_listx~.
Qed.

Lemma Forall2_rev_eq : forall P r s,
  Forall2 P r s = Forall2 P (rev r) (rev s).
Proof using.
  intros. extens. iff M.
  { applys~ Forall2_rev. }  
  { rewrite <- (rev_rev r). rewrite <- (rev_rev s). applys~ Forall2_rev. }
Qed.

Lemma Forall2_take : forall P n r s,
  Forall2 P r s ->
  Forall2 P (take n r) (take n s).
Proof using. intros P n. induction n; introv H; inverts H; rew_listx~. Qed.

Lemma Forall2_drop : forall P n r s,
  Forall2 P r s ->
  Forall2 P (drop n r) (drop n s).
Proof using. intros P n. induction n; introv H; inverts H; rew_listx~. Qed.

Lemma Forall2_map_l : forall f P l,
  (forall y, P (f y) y) ->
  Forall2 P (map f l) l.
Proof using. introv I. induction l; rew_listx~. Qed.

Lemma Forall2_map_r : forall f P l,
  (forall x, P x (f x)) ->
  Forall2 P l (map f l).
Proof using. introv I. induction l; rew_listx~. Qed.

Lemma Forall2_Nth_inv : forall P r s n x y,
  Forall2 P r s ->
  Nth n r x ->
  Nth n s y ->
  P x y.
Proof using. 
  introv F N1 N2. gen n. 
  induction~ F; introv N1 N2; inverts N1; inverts* N2. 
Qed.

Lemma Forall2_nth_inv : forall {IA:Inhab A} {IB:Inhab B} P r s n,
  Forall2 P r s ->
  n < length r ->
  P (nth n r) (nth n s).
Proof using. 
  introv F N. forwards: Forall2_inv_length F. 
  applys Forall2_Nth_inv n F; applys Nth_nth; math.
Qed.

Lemma Forall2_of_forall_nth : forall {IA:Inhab A} {IB:Inhab B} P r s,
  (forall n, n < length r -> P (nth n r) (nth n s)) ->
  length r = length s ->
  Forall2 P r s.
Proof using.
  introv H E. gen s. induction r; intros; destruct s; tryfalse.
  { auto. }
  { rew_list in E. constructors.
    { applys H 0. rew_list. math. }
    { applys~ IHr. introv N. applys H (S n). rew_list. math. } }
Qed.

End Forall2.


(* ---------------------------------------------------------------------- *)
(* ** Forall3 *)

(** [Forall3] is similar to [Forall2] except that it relates three lists. *)

Inductive Forall3 A B C (P : A -> B -> C -> Prop)
  : list A -> list B -> list C -> Prop :=
  | Forall3_nil :
      Forall3 P nil nil nil
  | Forall3_cons : forall l1 l2 l3 x1 x2 x3,
      P x1 x2 x3 -> 
      Forall3 P l1 l2 l3 ->
      Forall3 P (x1::l1) (x2::l2) (x3::l3).

(* LATER: lemmas about Forall3 *)


(* ---------------------------------------------------------------------- *)
(* ** Exists *)

(** [exists P l] asserts that there exists a value in the
    list [l] that satisfied the predicate [P]. *)

Inductive Exists A (P:A->Prop) : list A -> Prop :=
  | Exists_head : forall l x,
      P x -> 
      Exists P (x::l)
  | Exists_tail : forall l x,
      Exists P l ->
      Exists P (x::l).

Section Exists.
Variables A : Type.
Implicit Types l : list A.
Implicit Types P : A -> Prop.
Hint Constructors Exists.

(* Rewriting *)

Lemma Exists_nil_eq : forall P,
  Exists P nil = False.
Proof using. intros. extens. iff M. { invert* M. } { false. } Qed.

Lemma Exists_cons_eq : forall P l x,
  Exists P (x::l) = (P x \/ Exists P l).
Proof using. intros. extens. iff M. { inverts* M. } { destruct* M. } Qed.

Lemma Exists_one_eq : forall P x,
  Exists P (x::nil) = P x.
Proof using. intros. extens. rewrite Exists_cons_eq. rewrite* Exists_nil_eq. Qed.

Lemma Exists_app_eq : forall P l1 l2,
  Exists P (l1++l2) = (Exists P l1 \/ Exists P l2).
Proof using.
  intros. extens. induction l1; rew_list.
  { iff M [M|M]. { autos*. } { inverts~ M. } { autos*. } }
  { iff M [M|M].
    { inverts* M. }
    { inverts M. { auto. } { applys* Exists_tail. } }
    { applys* Exists_tail. } }
Qed.

Lemma Exists_last_eq : forall P l x,
  Exists P (l&x) = (P x \/ Exists P l).
Proof using.
  intros. extens. rewrite Exists_app_eq. rewrite Exists_cons_eq.
  rewrite* Exists_nil_eq.
Qed.

(* Constructors *)

Lemma Exists_app_l : forall P l1 l2,
  Exists P l1 ->
  Exists P (l1++l2).
Proof using. intros. rewrite* Exists_app_eq. Qed.

Lemma Exists_app_r : forall P l1 l2,
  Exists P l2 ->
  Exists P (l1++l2).
Proof using. intros. rewrite* Exists_app_eq. Qed.

Lemma Exists_last : forall P l x,
  Exists P l ->
  P x ->
  Exists P (l&x).
Proof using. intros. rewrite* Exists_last_eq. Qed.

(* Inversion *)

Lemma Exists_nil_inv : forall P,
  Exists P nil -> 
  False.
Proof using. introv H. rewrite* Exists_nil_eq in H. Qed.

Lemma Exists_cons_inv : forall P l x,
  Exists P (x::l) -> 
  P x \/ Exists P l.
Proof using. introv H. rewrite* Exists_cons_eq in H. Qed.

Lemma Exists_one_inv : forall P x,
  Exists P (x::nil) -> 
  P x.
Proof using. introv H. rewrite* Exists_one_eq in H. Qed.

Lemma Exists_app_inv : forall P l1 l2,
  Exists P (l1++l2) ->
  Exists P l1 \/ Exists P l2.
Proof using. introv H. rewrite* Exists_app_eq in H. Qed.

Lemma Exists_last_inv : forall P l x,
  Exists P (l&x) ->
  P x \/ Exists P l.
Proof using. introv H. rewrite* Exists_last_eq in H. Qed.

(* Interactions *)

Lemma Exists_eq_exists_mem : forall P l,
  Exists P l <-> (exists x, mem x l /\ P x).
Proof using. 
  Hint Constructors mem.
  introv. induction l as [|y l'].
  { iff M (x&M&H). { inverts M. } { inverts M. } }
  { iff M (x&M&H).
    { inverts M as N.
      { exists* y. }
      { forwards (x&M&H): (proj1 IHl') N. exists* x. } }
    { destruct (mem_cons_inv M) as [N|N].
      { subst*. }
      { applys* Exists_tail. } } }
Qed.

Lemma mem_Exists : forall P l x,
  mem x l ->
  P x ->
  Exists P l.
Proof using. introv M H. rewrite* Exists_eq_exists_mem. Qed.

Lemma mem_Exists_eq : forall P l x,
  mem x l = Exists (= x) l.
Proof using.
  intros. extens. rewrite* Exists_eq_exists_mem. iff M (y&?&?); subst*.
Qed.

Lemma Nth_Exists : forall P n l x,
  Nth n l x ->
  P x ->
  Exists P l.
Proof using. introv M H. applys* mem_Exists. applys* Nth_mem. Qed.

Lemma nth_Exists : forall {IA:Inhab A} P n l,
  P (nth n l) ->
  n < length l ->
  Exists P l.
Proof using. introv H N. applys* Nth_Exists n. applys~ Nth_nth. Qed.

Lemma Exists_rev : forall P l,
  Exists P l ->
  Exists P (rev l).
Proof using.
  introv E. induction l.
  { auto. }
  { rew_list. rewrite Exists_last_eq. inverts* E. }
Qed.

Lemma Exists_rev_eq : forall P l,
  Exists P (rev l) = Exists P l.
Proof using.
  intros. extens. iff M.
  { rewrite <- rev_rev. applys~ Exists_rev. }
  { applys~ Exists_rev. }
Qed.

Lemma Exists_pred_incl : forall P Q l,
  Exists P l -> 
  pred_incl P Q ->
  Exists Q l.
Proof using. introv. induction l; introv H L; inverts* H. Qed.

Lemma Exists_filter_pred_incl : forall P Q l,
  Exists P l ->
  pred_incl P Q ->
  Exists P (filter Q l).
Proof using.
  introv M N. induction M; rew_listx.
  { forwards*: N. case_if*. }
  { case_if~. } 
Qed.

Lemma Exists_filter_same : forall P l,
  Exists P l ->
  Exists P (filter P l).
Proof using. introv M. applys* Exists_filter_pred_incl. applys pred_incl_refl. Qed.

Lemma Exists_take_inv : forall P n l,
  Exists P (take n l) ->
  Exists P l.
Proof using.
  introv E. forwards (q&K): take_is_prefix n l. 
  rewrite K. rewrite* Exists_app_eq.
Qed.

Lemma Exists_drop_inv : forall P n l,
  Exists P (drop n l) ->
  Exists P l.
Proof using.
  introv E. forwards (q&K): drop_is_suffix n l. 
  rewrite K. rewrite* Exists_app_eq.
Qed.

Lemma Exists_inv_middle_first : forall P l,
  Exists P l ->
  exists l1 x l2,
       l = l1++x::l2
    /\ Forall (fun x => ~ P x) l1
    /\ P x.
Proof using.
  introv E. induction E.
   exists (@nil A) x l. splits~. constructors~.
   lets (l1&x'&l2&E1&F&HP): (rm IHE). tests Px: (P x).
    exists (@nil A) x l. splits~. constructors~.
    substs. exists (x :: l1) x' l2. splits~. constructors~.
Qed.

(* LATER?
Lemma Exists_filter_inv : forall P Q l,
  Exists P (filter Q l) ->
  exists x, P x /\ Q x.
*)

End Exists.


(* ---------------------------------------------------------------------- *)
(* ** Exists2 *)

(** [Exists2 P L1 L2] asserts that there exists an index [n]
    such that the n-th element of [L1] and the n-th element
    of [L2] are related by the binary relation [P]. *)

Inductive Exists2 A1 A2 (P : A1 -> A2 -> Prop)
  : list A1 -> list A2 -> Prop :=
  | Exists2_here : forall l1 l2 x1 x2,
      P x1 x2 -> 
      Exists2 P (x1::l1) (x2::l2)
  | Exists2_next : forall l1 l2 x1 x2,
      Exists2 P l1 l2 ->
      Exists2 P (x1::l1) (x2::l2).

(* LATER: lemmas about Exists2 *)


(* ---------------------------------------------------------------------- *)
(* ** Assoc as a relation *)

(** [Assoc x v l] asserts that [(x,v)] the first pair of the
    form [(x,_)] in [l] *)

Inductive Assoc A B (x:A) (v:B) : list (A*B) -> Prop :=
  | Assoc_here : forall l ,
      Assoc x v ((x,v)::l)
  | Assoc_next : forall y l w,
      Assoc x v l -> 
      x <> y ->
      Assoc x v ((y,w)::l).

(* LATER: lemmas about Assoc *)


(* ---------------------------------------------------------------------- *)
(** * Fold *)

(** WARNING: EXPERIMENTAL SECTION *)

Definition fold A B (m:monoid_op B) (f:A->B) (L:list A) : B :=
  fold_right (fun x acc => monoid_oper m (f x) acc) (monoid_neutral m) L.

Section Fold.
Variables (A B:Type).
Implicit Types m : monoid_op B.
Implicit Types l : list A.
Implicit Types f g : A->B.

Lemma fold_nil : forall m f,
  fold m f nil = monoid_neutral m.
Proof using. auto. Qed.

Lemma fold_cons : forall m f x l,
  fold m f (x::l) = monoid_oper m (f x) (fold m f l).
Proof using. auto. Qed.

Lemma fold_one : forall m f x,
  Monoid m ->
  fold m f (x::nil) = f x.
Proof using.
  intros. rewrite fold_cons, fold_nil. rewrite~ monoid_neutral_r.
Qed.

Lemma fold_app : forall m f l1 l2,
  Monoid m ->
  fold m f (l1 ++ l2) = monoid_oper m (fold m f l1) (fold m f l2).
Proof using.
  unfold fold. intros. rewrite fold_right_app. gen l2.
  induction l1; intros.
  repeat rewrite fold_right_nil. rewrite~ monoid_neutral_l.
  repeat rewrite fold_right_cons. rewrite <- monoid_assoc. fequals.
Qed.

Lemma fold_last : forall m f x l,
  Monoid m ->
  fold m f (l & x) = monoid_oper m (fold m f l) (f x).
Proof using.
  intros. rewrite~ fold_app. rewrite fold_cons.
  rewrite fold_nil. rewrite monoid_neutral_r. auto.
Qed.

Lemma fold_congruence : forall m f g l,
  (forall x, mem x l -> f x = g x) ->
  fold m f l = fold m g l.
Proof using.
  Hint Constructors mem.
  intros. unfold fold.
  induction l as [| x l' ]; intros; simpl.
  { eauto. }
  { rew_listx. fequals. applys~ H. eauto. }
Qed.

(* TODO: reformulate using a definition of list permutation, *)
Lemma fold_equiv_step : forall m f l a,
  Comm_monoid m ->
  noduplicates l ->
  mem a l ->
  exists l',
     fold m f l = fold m f (a::l')
  /\ (forall x, mem x l <-> mem x (a::l'))
  /\ noduplicates (a::l').
Proof using. (* TODO: cleanup *)
  introv Hm. induction l as [|b t]; introv DL La. inverts La.
  tests: (a = b).
    exists t. splits*.
    inverts La. false. inverts DL as DLb DT. forwards~ (L'&EL'&EQ&DL'): IHt.
     exists (b::L'). splits.
       do 3 rewrite fold_cons. rewrite EL'.
        rewrite fold_cons. do 2 rewrite monoid_assoc.
        rewrite~ (monoid_comm (f b)).
       intros x. specializes EQ x. rewrite mem_cons_eq in EQ.
        do 3 rewrite mem_cons_eq. autos*.
       inverts DL'. constructors.
         introv N. inverts N. false. false.
         constructors~. introv N. applys DLb. rewrite EQ. constructors~.
Qed.

(* TODO: reformulate using a definition of list permutation,
   which is entailed by the premises 2,3 and 4. *)
Lemma fold_equiv : forall m f l1 l2,
  Comm_monoid m ->
  noduplicates l1 ->
  noduplicates l2 ->
  (forall x, mem x l1 <-> mem x l2) ->
  fold m f l1 = fold m f l2.
Proof using. (* TODO: cleanup *)
  intros m f l1. induction l1; introv HM D1 D2 EQ.
  cuts_rewrite (l2 = nil). rewrite~ fold_nil.
    destruct l2; auto. forwards~ M: (proj2 (EQ a)). inverts M.
  inverts D1. asserts L2a: (mem a l2). rewrite~ <- EQ.
   forwards* (l2'&V2'&EQ'&D2'): fold_equiv_step f L2a.
   rewrite V2'. do 2 rewrite fold_cons.
  inverts D2'.
  rewrite~ (IHl1 l2'). intros.
  tests: (x = a).
    iff; auto_false*.
  asserts_rewrite (mem x l1 = mem x (a::l1)).
    extens. iff~ M. inverts~ M. false.
  asserts_rewrite (mem x l2' = mem x (a::l2')).
    extens. iff~ M. inverts~ M. false.
  rewrite EQ. rewrite* EQ'.
Qed.

End Fold.

(* TODO: decide later whether TLC should rely on [Proper] *)
Lemma fold_pointwise : forall B m (leB : B -> B -> Prop),
  Monoid m ->
  refl leB ->
  Proper (leB ++> leB ++> leB) (monoid_oper m) ->
  forall A (l : list A),
  forall (f f' : A -> B),
  (forall x, mem x l -> leB (f x) (f' x)) ->
  leB (fold m f l) (fold m f' l).
Proof using. (* TODO: cleanup *)
  Hint Constructors mem.
  introv HM HR HP. induction l; introv HL.
  do 2 rewrite fold_nil. applys HR.
  do 2 rewrite fold_cons. apply HP. applys~ HL. applys~ IHl.
Qed.

Opaque fold.


(* ---------------------------------------------------------------------- *)
(* ** Induction principle on lists 
     -- TODO cleanup and move to a different file *)

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

Arguments list_sub {A}.
Hint Constructors list_sub.
Hint Resolve list_sub_wf : wf.

(** Induction on all but last item *)

Lemma list_ind_last : forall (A : Type) (P : list A -> Prop),
  P nil ->
  (forall (a : A) (l : list A), P l -> P (l & a)) ->
  forall l : list A, P l.
Proof using.
  introv H1 H2. intros. induction_wf IH: (wf_measure (@length A)) l.
  lets [E|(x&l'&E)]: (last_case l); subst. auto.
  unfolds measure. rewrite length_last in IH. auto with maths.
Qed.


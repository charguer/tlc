(* ---under construction


(**************************************************************************
* TLC: A library for Coq                                                  *
* Executable functions over lists                                         *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import Coq.Classes.Morphisms. (* for [Proper] instances *)
From TLC Require Import LibTactics LibLogic LibReflect LibOperation
 LibProd LibOption LibNat LibInt LibWf LibMonoid LibRelation LibList.
Local Open Scope nat_scope.
Local Open Scope comp_scope.
Global Close Scope list_scope.



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
(** * Comparable *)

Fixpoint list_compare `{Comparable A} (l1 l2 : list A) :=
  match l1,l2 with
  | nil, nil => true
  | x1::t1, x2::t2 => decide (x1 = x2) && list_compare t1 t2
  | _, _ => false
  end.

Global Instance list_comparable : forall (A : Type),
  Comparable A -> Comparable (list A).
Proof using.
  introv CA. applys comparable_beq list_compare. intros l1.
  induction l1; intros l2; destruct l2; simpl; rew_refl; iff H; inverts~ H;
   tryfalse; auto; try congruence.
   fequals. applys* IHl1.
   split~. applys* IHl1.
Qed.

Global Instance list_eq_nil_decidable : forall (A : Type) (l : list A),
  Decidable (l = nil).
Proof using.
  intros. applys decidable_make (match l with nil => true | _ => false end).
  extens. destruct l; iff; rew_refl in *; auto_false*.
Qed.




(* ---------------------------------------------------------------------- *)
(** ** Filter_bool *)

Section Filterb.
Variables (A : Type).
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types f : A -> bool.

Definition filterb f l :=
  fold_right (fun x acc => if f x then x::acc else acc) (@nil A) l.

Lemma filterb_nil : forall f,
  filterb f nil = nil.
Proof using. auto. Qed.

Lemma filterb_cons : forall f x l,
    filterb f (x::l) 
  = if f x then x :: filterb f l else filterb f l.
Proof using. auto. Qed.

Lemma filterb_app : forall f l1 l2,
  filterb f (l1 ++ l2) = filterb f l1 ++ filterb f l2.
Proof using.  
  (* LATER: investigate how to factorise with proof of map_app *)
  intros. unfold filterb.
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

Lemma filterb_last : forall f x l,
  filterb f (l & x) = filterb f l ++ (if f x then x::nil else nil).
Proof using. intros. rewrite~ filterb_app. Qed.

(* LATER: add length_filterb *)

End Filterb.

Opaque filterb.  



(* ---------------------------------------------------------------------- *)
(** ** Mem *)

Section Memb.
Variables (A : Type).
Implicit Types x k : A.
Implicit Types l : list A.

Fixpoint memb x l :=
  match l with
  | nil => false
  | y::l' => (x '= y) || memb x l'
  end.

Lemma memb_nil : forall k,
  memb k nil = false.
Proof using. auto. Qed.

Lemma memb_cons : forall k x l,
  memb k (x::l) = (k '= x) || (memb k l).
Proof using. auto. Qed.

Lemma memb_app : forall f l1 l2,
  memb f (l1 ++ l2) = (memb f l1) || memb f l2.
Proof using.
  intros. induction l1.
  { rew_bool. rew_list~. }
  { rew_list. do 2 rewrite memb_cons. rewrite~ IHl1. rewrite~ assoc_or. }
Qed.

Lemma memb_last : forall k x l,
  memb k (l & x) = (k '= x) || (memb k l).
Proof using.
  intros. rewrite memb_app. rewrite memb_cons.
  rewrite LibBool.comm_or. rew_bool. auto.
Qed.

Lemma memb_cons_eq : forall x l,
  memb x (x::l) = true.
Proof using. intros. rewrite memb_cons. rewrite~ eqb_self. Qed.

Lemma memb_last_eq : forall x l,
  memb x (l & x) = true.
Proof using. intros. rewrite memb_last. rewrite~ eqb_self. Qed.

Lemma memb_rev : forall l x,
  memb x (rev l) = memb x l.
Proof using.
  introv. induction~ l.
  { rewrite memb_cons. rew_list. rewrite memb_last.
    extens. rew_refl. rewrite* IHl. }
Qed.

Lemma memb_filter : forall l f a,
  memb a (filter f l) = (memb a l && f a).
Proof using.
  introv. extens. induction l.
  { rewrite filter_nil. iff I; false I. }
  { rewrite filter_cons. cases_if; iff I; rewrite memb_cons in *.
    { rew_refl in *. inverts I as I; splits*. }
    { lets (I'&D): (rm I). simpls. rew_refl in *. inverts* I'. }
    { rewrite IHl in I. splits*. rew_refl. right*. }
    { lets (I'&D): (rm I). rew_refl in *. inverts* I'. false*. } }
Qed.

End Memb.

Opaque memb.

Hint Rewrite memb_nil memb_cons memb_app memb_last
 memb_cons_eq memb_last_eq : rew_lists.


Global Instance mem_decidable : forall `{Comparable A} (x : A) (l : list A),
   Decidable (mem x l).
Proof using.
  intros. applys decidable_make (mem_decide x l). extens. rew_refl.
  induction l; simpl.
  iff E. false. inverts E.
  case_if.
    iff E; subst*.
    iff E. constructors*. inverts* E.
Qed.


Lemma mem_memb : forall l x,
  mem x l = memb x l.
Proof using.
  introv. extens. induction l; iff I; inverts I as I;
    simpls; fold_bool; rew_refl in *; autos*.
   inverts* I.
Qed.

Fixpoint mem_decide `{Comparable A} (x : A) (l : list A) :=
  match l with
  | nil => false
  | y::l' => ifb x = y then true else mem_decide x l'
  end.



(* ---------------------------------------------------------------------- *)
(** ** Remove *)

Definition remove `{CA:Comparable A} (x:A) (l:list A) :=
  filter (fun y => decide (y <> x)) l.

(* LATER: properties of [remove] *)

Arguments remove [A] {CA}.
Opaque remove.


(* ---------------------------------------------------------------------- *)
(** ** Removes *)

Fixpoint removes `{CA:Comparable A} (l1 l2:list A) :=
  match l1 with
  | nil => l2
  | x::l1' => removes l1' (remove x l2)
  end.

(* LATER: properties of [removes] *)

Arguments removes [A] {CA}.
Opaque removes.






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



(* ---------------------------------------------------------------------- *)

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




Global Instance Forall_decidable : forall (A : Type) (P : A->Prop) (l : list A),
  (forall x, Decidable (P x)) -> Decidable (Forall P l).
Proof using.  (*todo: optimize proof *)
  introv H. applys decidable_make
    (fold_left (fun a b => and b (decide (P a))) true l).
  tests: (Forall P l).
   rewrite~ isTrue_true. fold_bool.
    induction~ C. rew_list. (* --TODO: rewrite neutral_l_and. *) simpl. case_if~.
   rewrite~ isTrue_false. fold_bool.
    induction~ l.
     false C. constructor~.
     rew_list. simpl. case_if~.
      apply~ IHl. intro F; apply C. constructor~.
      clear C IHl. induction* l.
Qed.



(* ********************************************************************** *)
(** * Association lists *)


--does not compile yet--
Hint Rewrite app_cons app_nil_l app_nil_r app_assoc
 app_cons_one
 mem_nil mem_cons mem_app mem_last
 mem_cons_eq mem_last_eq
 keys_nil keys_cons keys_app keys_last
 assoc_cons assoc_here : rew_lists.


(* ---------------------------------------------------------------------- *)
(** ** Operations *)

Section Assoc.
Context {A B : Type}.
Variables (IB:Inhab B) (CA:Comparable A).
Implicit Types x : A.
Implicit Types l : list (A*B).

Fixpoint assoc k l : B :=
  match l with
  | nil => arbitrary
  | (x,v)::l' => ifb x = k then v else assoc k l'
  end.

Definition mem_assoc k :=
  exists_st (fun p:A*B => k '= fst p).

Definition keys :=
  @map (A*B) A (@fst _ _).

Fixpoint remove_assoc k l : list (A*B) :=
  match l with
  | nil => nil
  | (x,v)::l' =>
      ifb k = x
        then remove_assoc k l'
        else (x,v)::(remove_assoc k l')
  end.

End Assoc.

Arguments assoc [A] [B] {IB} {CA}.
Arguments mem_assoc [A] [B].
Arguments keys [A] [B].
Arguments remove_assoc [A] [B] {CA}.


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Section AssocProperties.
Variable (A B : Type) (IB:Inhab B) (CA:Comparable A).
Implicit Types x : A.
Implicit Types l : list (A*B).

Lemma assoc_cons : forall k x y l,
  assoc k ((x,y)::l) = ifb x = k then y else assoc k l.
Proof using. auto. Qed.
Lemma assoc_here : forall x y l,
  assoc x ((x,y)::l) = y.
Proof using. intros. simpl. case_if~. Qed.
Lemma assoc_next : forall x y k l,
  k '<> x -> assoc k ((x,y)::l) = assoc k l.
Proof using. intros. simpl. fold_prop. case_if~. Qed.

Lemma keys_nil :
  keys (@nil (A*B)) = nil.
Proof using. auto. Qed.
Lemma keys_cons : forall x y l,
  keys ((x,y)::l) = x :: (keys l).
Proof using. auto. Qed.
Lemma keys_app : forall l1 l2,
  keys (l1 ++ l2) = keys l1 ++ keys l2.
Proof using. intros. applys map_app. Qed.
Lemma keys_last : forall x y l,
  keys (l & (x,y)) = (keys l) & x.
Proof using. intros. rewrite~ keys_app. Qed.

Lemma remove_assoc_nil : forall x,
  remove_assoc x nil = (@nil (A*B)).
Proof using. auto. Qed.
Lemma remove_assoc_cons : forall x x' y l,
  remove_assoc x ((x',y)::l) =
    ifb x = x' then remove_assoc x l else (x',y)::remove_assoc x l.
Proof using. auto. Qed.

Lemma assoc_remove_assoc : forall x x' l,
  x <> x' ->
  assoc x (remove_assoc x' l) = assoc x l.
Proof using.
  introv D. induction l.
   reflexivity.
   destruct a. simpl. do 2 case_if~; simpl; case_if~.
Qed.

End AssocProperties.

Section MemAssocProperties.

Lemma assoc_mem_assoc : forall A B `{Inhab B} `{Comparable A} (l : list (A * B)) a,
  mem_assoc a l ->
  mem (a, assoc a l) l.
Proof using.
  introv M. induction l as [|[a' b'] l]; tryfalse.
  rewrite mem_cons. rewrite assoc_cons. rew_refl. cases_if.
   substs*.
   right. apply IHl.
    do 2 unfolds in M. simpl in M. rew_refl in M. inverts* M.
Qed.

Lemma mem_assoc_assoc : forall A B `{Inhab B} `{Comparable A} (l : list (A * B)) a b,
  assoc a l = b ->
  mem_assoc a l ->
  mem (a, b) l.
Proof using. introv E I. substs. apply~ assoc_mem_assoc. Qed.

Lemma mem_assoc_map_fst : forall A B (l : list (A * B)) a,
  mem_assoc a l = mem a (map fst l).
Proof using.
  extens. induction l as [|[a' b'] l]; iff I; tryfalse.
   do 2 unfolds in I. rewrite fold_right_cons in I. rewrite map_cons, mem_cons.
    rew_refl in *. inverts I as I.
      right. apply~ IHl.
      left~.
   rewrite map_cons in I. do 2 unfolds. simpls. rewrite fold_right_cons.
    rewrite mem_cons in I. rew_refl in *. inverts I as I.
      right~.
      left. apply~ IHl.
Qed.

Lemma mem_assoc_cons : forall A B (l : list (A * B)) a e,
  mem_assoc a (e :: l) = (a '= fst e) || mem_assoc a l.
Proof using.
  introv. extens. iff M.
   do 2 unfolds in M. rewrite fold_right_cons in M. rew_refl. rew_refl* in M.
   rew_refl in M. inverts M as M.
    destruct e as [a b]. do 2 unfolds. rewrite fold_right_cons. rew_refl*.
    do 2 unfolds. rewrite fold_right_cons. rew_refl*.
Qed.

Lemma mem_assoc_nil : forall A B a,
  mem_assoc a (nil : list (A * B)) = false.
Proof using. autos*. Qed.

Lemma mem_mem_assoc : forall A B (l : list (A * B)) a b,
  mem (a, b) l ->
  mem_assoc a l.
Proof using.
  introv I. induction~ l. rewrite mem_cons in I. rewrite mem_assoc_cons.
  rew_refl in *. inverts* I.
Qed.

Lemma assoc_eq_mem_assoc : forall A B `{Inhab B} `{Comparable A} (l : list (A * B)) a,
  mem (a, assoc a l) l = mem_assoc a l.
Proof using.
  introv. induction l as [|[a' b'] l].
   reflexivity.
   rewrite mem_cons. simpl. extens.
   case_if; iff I; rewrite mem_assoc_cons in *; rew_refl in *.
    repeat inverts I as I.
     autos~.
     cbv beta. rewrite* <- IHl.
     inverts I; substs*.
     rew_refl in I. inverts I; tryfalse. right. rewrite~ <- IHl.
    rew_refl. inverts I; tryfalse~. right. rewrite~ IHl.
Qed.

Lemma mem_assoc_exists_mem : forall A B (l : list (A * B)) a,
  mem_assoc a l ->
  exists b, mem (a, b) l.
Proof using.
  introv M. induction l as [|[a' b'] l]; tryfalse.
  do 2 unfolds in M. rewrite fold_right_cons in M. rew_refl in M. inverts M as M.
   forwards (b&M'): (rm IHl) (rm M). exists b. rewrite mem_cons. rew_refl*.
   exists b'. simpl. rewrite mem_cons. rew_refl*.
Qed.

Lemma app_mem_assoc : forall A B (l1 l2 : list (A * B)) a,
  mem_assoc a (l1 ++ l2) ->
  mem_assoc a l1 \/ mem_assoc a l2.
Proof using.
  introv M. lets (b&M'): mem_assoc_exists_mem (rm M). rewrite mem_app in M'.
  rew_refl in M'. inverts M' as M.
   left. apply* mem_mem_assoc.
   right. apply* mem_mem_assoc.
Qed.

Lemma keys_mem_assoc : forall A B (l : list (A * B)) a,
  mem a (keys l) = mem_assoc a l.
Proof using. introv. unfold keys. rewrite~ <- mem_assoc_map_fst. Qed.

Lemma mem_assoc_remove_assoc_neq : forall A B `{Comparable A} x x' (l : list (A * B)),
  x <> x' ->
  mem_assoc x (remove_assoc x' l) = mem_assoc x l.
Proof using.
  introv N. induction l.
   reflexivity.
   destruct a. rewrite remove_assoc_cons. case_if~.
    rewrite mem_assoc_cons. rewrite IHl. extens. rew_refl. iff* I.
     inverts~ I. false*.
    repeat rewrite mem_assoc_cons. extens. rew_refl. iff* I.
     inverts~ I. rewrite IHl in *. autos*.
     inverts~ I. rewrite* IHl.
Qed.

Lemma mem_assoc_remove_assoc_eq : forall A B `{Comparable A} x (l : list (A * B)),
  mem_assoc x (remove_assoc x l) = false.
Proof using.
  introv. induction l.
   reflexivity.
   destruct a. simpl. case_if~. rewrite mem_assoc_cons. fold_bool. rew_refl in *.
    introv [E|M]; apply IHl; substs*.
Qed.

End MemAssocProperties.

Arguments assoc : simpl never.
Arguments mem_assoc : simpl never.
Arguments keys : simpl never.
Arguments remove_assoc : simpl never.

(* DEPRECATED *)
Definition count (f : A->bool) :=
  fold_right (fun x acc => (if f x then 1 else 0) + acc) 0.


*)
(**************************************************************************
* TLC: A library for Coq                                                  *
* Lists                                                                   *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import Coq.Classes.Morphisms. (* for [Proper] instances *)
Require Import LibTactics LibLogic LibReflect LibOperation
 LibProd LibOption LibNat LibInt LibWf LibStruct LibRelation.
Require Export List.
Local Open Scope nat_scope.
Local Open Scope comp_scope.


(* ********************************************************************** *)
(** Fixing implicit arguments *)

Implicit Arguments nil [[A]].
Implicit Arguments cons [[A]].


(* ********************************************************************** *)
(** * Inhabited *)

Instance list_inhab : forall A, Inhab (list A).
Proof using. intros. apply (prove_Inhab nil). Qed.


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

(** Special case for comparing against the empty list *)

Global Instance list_eq_nil_decidable : forall (A : Type) (l : list A),
  Decidable (l = nil).
Proof using.
  intros. applys decidable_make (match l with nil => true | _ => false end).
  extens. destruct l; iff; rew_refl in *; auto_false*.
Qed.


(* ********************************************************************** *)
(** * Operations *)

(* ---------------------------------------------------------------------- *)
(** ** Operations on lists *)

Section Folds.
Context {A B : Type}.
Implicit Types l a b : list A.
Implicit Types x : A.

Fixpoint fold_right (f : A -> B -> B) (acc : B) l :=
  match l with
  | nil => acc
  | x::L' => f x (fold_right f acc L')
  end.

Fixpoint fold_left (f : A -> B -> B) (acc : B) l :=
  match l with
  | nil => acc
  | x::L' => fold_left f (f x acc) L'
  end.

End Folds.

Section Operations.
Variables (A B C : Type) (IA : Inhab A) (CA : Comparable A).
Implicit Types l a b : list A.
Implicit Types x : A.

Definition map (f : A -> C) :=
  nosimpl (fold_right (fun x acc => (f x)::acc) (@nil C)).

Definition append l1 l2 :=
  nosimpl (fold_right (fun x (acc:list A) => x::acc) l2 l1).

Definition concat :=
  nosimpl (fold_right append (@nil A)).

Definition rev :=
  nosimpl (fold_left (fun x acc => x::acc) (@nil A)).

Definition length :=
  nosimpl (fold_right (fun x acc => 1+acc) 0).

Definition filter (f : predb A) :=
  nosimpl (fold_right (fun x acc => if f x then x::acc else acc) (@nil A)).

Definition for_all (f : predb A) :=
  nosimpl (fold_right (fun x acc => acc && (f x)) true).

Definition exists_st (f : predb A) :=
  nosimpl (fold_right (fun x acc => acc || (f x)) false).

Definition count (f : predb A) :=
  nosimpl (fold_right (fun x acc => (if f x then 1 else 0) + acc) 0).

(* The head of a list is its first element. *)

Definition head (xs : list A) : option A :=
  match xs with
  | nil => None
  | x :: _ => Some x
  end.

(* The tail of a list is everything beyond its first element. *)

Definition tail (xs : list A) : list A :=
  match xs with
  | nil => nil
  | _ :: xs => xs
  end.

(* These functions are known as [List.hd_error] and [List.tl] in Coq's
   standard library. *)

Lemma head_hd_error (xs : list A) : head xs = List.hd_error xs.
Proof. destruct xs; reflexivity. Qed.

Lemma tail_tl (xs : list A) : tail xs = List.tl xs.
Proof. destruct xs; reflexivity. Qed.

(* The empty list, and only the empty list, has no head. *)

Lemma use_None_head (xs : list A) : None = head xs -> xs = nil.
Proof. destruct xs; simpl; congruence. Qed.

Lemma use_Some_head x (xs : list A) : Some x = head xs -> xs <> nil.
Proof. destruct xs; simpl; congruence. Qed.

(* No list is cyclic. *)

Lemma no_cyclic_list:
  forall (xs : list A) x,
  x :: xs = xs ->
  False.
Proof using.
  induction xs; simpl; introv h.
  { congruence. }
  { injection h. clear h. intros h ?. subst x. eauto. }
Qed.

(* Only the empty list is its own tail. *)

Lemma tail_self_inv:
  forall (xs : list A),
  tail xs = xs ->
  xs = nil.
Proof using.
  destruct xs; simpl; intros.
  { eauto. }
  { false. eauto using no_cyclic_list. }
Qed.

Fixpoint mem x l :=
  match l with
  | nil => false
  | y::l' => (x '= y) || mem x l'
  end.

Definition remove x :=
  filter (fun y => decide (y <> x)).

Fixpoint removes l2 l1 :=
  match l2 with
  | nil => l1
  | x::l2' => removes l2' (remove x l1)
  end.

Fixpoint split (l: list (A*B)) : (list A * list B) :=
  match l with
  | nil => (nil,nil)
  | (a,b)::l' => let (la,lb) := split l' in (a::la, b::lb)
  end.

Fixpoint combine (la : list A) (lb : list B) : list (A*B) :=
  match la with
  | nil => nil
  | a::la' =>
    match lb with
    | nil => arbitrary
    | b::lb' => (a,b)::(combine la' lb')
    end
  end.

(* TODO: a function that combines drop & take *)

Fixpoint drop (n:nat) (l:list A) : list A :=
  match n with
  | 0 => l
  | S n' => match l with
    | nil => nil
    | a::l' => drop n' l'
    end
  end.

Fixpoint take (n:nat) (l:list A) : list A :=
  match n with
  | 0 => nil
  | S n' => match l with
    | nil => nil
    | a::l' => a::(take n' l')
    end
  end.

Fixpoint take_drop_last (l:list A) : (list A)*A :=
  match l with
  | nil => arbitrary
  | x::l' =>
    match l' with
    | nil => (nil,x)
    | _ => let (t,y) := take_drop_last l' in
           (x::t, y)
    end
  end.

Fixpoint nth_def (d:A) (n:nat) (l:list A) : A :=
  match l with
  | nil => d
  | x::l' =>
     match n with
     | 0 => x
     | S n' => nth_def d n' l'
     end
  end.

Definition nth := nth_def arbitrary.

Fixpoint update (n:nat) (v:A) (l:list A) {struct l} : list A :=
  match l with
  | nil => nil
  | x::l' =>
     match n with
     | 0 => v::l'
     | S n' => x::update n' v l'
     end
  end.

Fixpoint make (n:nat) (v:A) : list A :=
   match n with
   | 0 => nil
   | S n' => v :: make n' v
   end.

End Operations.

Definition fold A B (m:monoid_def B) (f:A->B) (L:list A) : B :=
  fold_right (fun x acc => monoid_oper m (f x) acc) (monoid_neutral m) L.

Implicit Arguments fold_left [[A] [B]].
Implicit Arguments fold_right [[A] [B]].
Implicit Arguments append [[A]].
Implicit Arguments concat [[A]].
Implicit Arguments rev [[A]].
Implicit Arguments length [[A]].
Implicit Arguments mem [[A]].
Implicit Arguments remove [[A] [CA]].
Implicit Arguments removes [[A] [CA]].
Implicit Arguments take_drop_last [[A] [IA]].
Implicit Arguments nth_def [[A]].
Implicit Arguments nth [[A] [IA]].
Implicit Arguments update [[A]].
Implicit Arguments make [[A]].
Implicit Arguments fold [[A] [B]].

(* todo: implicit arguments for the other functions *)


(* ---------------------------------------------------------------------- *)
(** ** Notation *)

(** [l1 ++ l2] concatenates two lists *)

Infix "++" := append (right associativity, at level 60) : list_scope.

(** [l & x] extends the list [l] with the value [x] at the right end *)

Notation "l & x" := (l ++ (x::nil))
  (at level 28, left associativity) : list_scope.


(* ********************************************************************** *)
(** * Properties of operations *)

Section AppFoldProperties.
Variables A B : Type.
Implicit Types x : A.
Implicit Types l : list A.

(* ---------------------------------------------------------------------- *)
(** ** App *)

Lemma app_cons : forall x l1 l2,
  (x::l1) ++ l2 = x::(l1++l2).
Proof using. auto. Qed.
Lemma app_nil_l : forall l,
  nil ++ l = l.
Proof using. auto. Qed.
Lemma app_nil_r : forall l,
  l ++ nil = l.
Proof using. induction l. auto. rewrite app_cons. fequals~. Qed.
Lemma app_assoc : forall l1 l2 l3,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof using.
  intros. induction l1.
  rewrite_all~ app_nil_l.
  rewrite_all~ app_cons. fequals~.
Qed.
Lemma app_last : forall x l1 l2,
  l1 ++ (x::l2) = (l1 & x) ++ l2.
Proof using. intros. rewrite~ app_assoc. Qed.
Lemma app_last_sym : forall x l1 l2,
  (l1 & x) ++ l2 = l1 ++ (x::l2).
Proof using. intros. rewrite~ <- app_last. Qed.
Lemma app_cons_one : forall x l,
  (x::nil) ++ l = x::l.
Proof using. auto. Qed.

Lemma app_cancel_l : forall l1 l2 l3,
  l1 ++ l2 = l1 ++ l3 -> l2 = l3.
Proof using.
  introv E. gen l2 l3. induction l1; introv E.
   repeat rewrite app_nil_l in E. autos~.
   repeat rewrite app_cons in E. inverts~ E.
Qed.

Lemma app_cancel_nil_l:
  forall (xs ys : list A),
  xs = xs ++ ys ->
  ys = nil.
Proof using.
  induction xs; introv h.
  { eauto. }
  { rewrite app_cons in h. injection h. eauto. }
Qed.


(* ---------------------------------------------------------------------- *)
(** ** FoldRight *)

Section FoldRight.
Variables (f : A -> B -> B) (i : B).
Lemma fold_right_nil :
  fold_right f i nil = i.
Proof using. auto. Qed.
Lemma fold_right_cons : forall x l,
  fold_right f i (x::l) = f x (fold_right f i l) .
Proof using. auto. Qed.
Lemma fold_right_app : forall l1 l2,
  fold_right f i (l1 ++ l2) = fold_right f (fold_right f i l2) l1.
Proof using.
  intros. induction l1. auto.
  rewrite app_cons. simpl. fequals~.
Qed.
Lemma fold_right_last : forall x l,
  fold_right f i (l & x) = fold_right f (f x i) l.
Proof using. intros. rewrite~ fold_right_app. Qed.
End FoldRight.

(* ---------------------------------------------------------------------- *)
(** ** FoldLeft *)

Section FoldLeft.
Variables (f : A -> B -> B) (i : B).
Lemma fold_left_nil :
  fold_left f i nil = i.
Proof using. auto. Qed.
Lemma fold_left_cons : forall x l,
  fold_left f i (x::l) = fold_left f (f x i) l.
Proof using. auto. Qed.
Lemma fold_left_app : forall l1 l2,
  fold_left f i (l1 ++ l2) = fold_left f (fold_left f i l1) l2.
Proof using.
  intros. gen i. induction l1; intros. auto.
  rewrite app_cons. simpl. rewrite~ IHl1.
Qed.
Lemma fold_left_last : forall x l,
  fold_left f i (l & x) = f x (fold_left f i l).
Proof using. intros. rewrite~ fold_left_app. Qed.
End FoldLeft.

End AppFoldProperties.

(* ---------------------------------------------------------------------- *)
(** ** Length *)

Section LengthProperties.
Variable A : Type.
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
  fold (length l2). induction l1; simple~.
Qed.
Lemma length_last : forall x l,
  length (l & x) = 1 + length l.
Proof using.
  intros. rewrite length_app.
  rewrite length_cons. rewrite length_nil.
  simpl. math.
Qed.
Lemma length_zero_inv : forall l,
  length l = 0%nat -> l = nil.
Proof using.
  destruct l. auto. rewrite length_cons. intros. false.
Qed.

End LengthProperties.

(* ---------------------------------------------------------------------- *)
(** ** Rev *)

Section OperationProperties.
Variable A : Type.
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
   induction l; intros; simpl. auto.
   rewrite IHl. rewrite (@IHl (a::nil)). rewrite~ app_last.
  asserts K2: (forall accu,
   fold_left (fun x acc => x :: acc) accu (l1 ++ l2) =
   fold_left (fun x acc => x :: acc) nil l2 ++
   fold_left (fun x acc => x :: acc) nil l1 ++ accu).
  induction l1; intros; simpl.
    do 2 rewrite app_nil_l. apply K1.
    rewrite IHl1. rewrite (@K1 l1 (a::nil)). rewrite~ app_last.
  lets K3: (@K2 nil). rewrite app_nil_r in K3. auto.
Qed.
Lemma rev_cons : forall x l,
  rev (x::l) = rev l & x.
Proof using. intros. rewrite <- app_cons_one. rewrite~ rev_app. Qed.
Lemma rev_last : forall x l,
  rev (l & x) = x::(rev l).
Proof using. intros. rewrite~ rev_app. Qed.
Lemma rev_cons_app : forall x l1 l2,
  rev (x :: l1) ++ l2 = rev l1 ++ (x::l2).
Proof using. intros. rewrite rev_cons. rewrite~ <- app_last. Qed.
Lemma app_rev_cons : forall x l1 l2,
  l1 ++ rev (x :: l2) = (l1 ++ rev l2) & x.
Proof using. intros. rewrite rev_cons. rewrite~ app_assoc. Qed.
Lemma rev_rev : forall l,
  rev (rev l) = l.
Proof using.
  induction l. auto. rewrite rev_cons. rewrite rev_last. fequals.
Qed.
Lemma length_rev : forall l,
  length (rev l) = length l.
Proof using.
  induction l. auto. rewrite rev_cons.
  rewrite length_last. rewrite~ length_cons.
Qed.

Lemma rev_inj : forall l1 l2,
  rev l1 = rev l2 ->
  l1 = l2.
Proof using. introv E. forwards E': f_equal E. repeat rewrite~ rev_rev in E'. Qed.

(** Lemma to rewrite a [fold_left] into a [fold_right]. **)
Lemma fold_left_eq_fold_right : forall B (f : A -> B -> B) i l,
  fold_left f i l = fold_right f i (rev l).
Proof using. introv. gen i. induction~ l. introv. rewrite rev_cons. rewrite* fold_right_last. Qed.

(** Lemma abuot app wich needs [rev] to be proven. **)
Lemma app_cancel_r : forall l1 l2 l3,
  l1 ++ l3 = l2 ++ l3 -> l1 = l2.
Proof using.
  introv E. gen l1 l2. induction l3; introv E.
   repeat rewrite app_nil_r in E. autos~.
   rewrite (app_last a l1) in E. rewrite (app_last a l2) in E.
    apply IHl3 in E. asserts E': (rev (l1 & a) = rev (l2 & a)).
      rewrite~ E.
    repeat rewrite rev_last in E'. inverts E' as E'.
    rewrite <- rev_rev. rewrite <- E'. rewrite~ rev_rev.
Qed.


(* ---------------------------------------------------------------------- *)
(** ** Mem *)

Section MemProp.
Implicit Types k : A.
Lemma mem_nil : forall k,
  mem k nil = false.
Proof using. auto. Qed.
Lemma mem_cons : forall k x l,
  mem k (x::l) = (k '= x) || (mem k l).
Proof using. auto. Qed.
Lemma mem_app : forall f l1 l2,
  mem f (l1 ++ l2) = (mem f l1) || mem f l2.
Proof using.
  intros. induction l1.
  rew_bool. rewrite~ app_nil_l.
  rewrite app_cons. simpl. rewrite~ IHl1.
  rewrite~ assoc_or.
Qed.
Lemma mem_last : forall k x l,
  mem k (l & x) = (k '= x) || (mem k l).
Proof using.
  intros. rewrite mem_app. simpl.
  rewrite LibBool.comm_or. rew_bool. auto.
Qed.
Lemma mem_cons_eq : forall x l,
  mem x (x::l) = true.
Proof using. intros. simpl. rewrite~ eqb_self. Qed.
Lemma mem_last_eq : forall x l,
  mem x (l & x) = true.
Proof using. intros. rewrite mem_last. rewrite~ eqb_self. Qed.

Lemma rev_mem : forall l x,
  mem x l = mem x (rev l).
Proof using.
  introv. induction~ l. simpls.
  rewrite rev_cons. rewrite mem_last. extens. rew_refl. rewrite* IHl.
Qed.

End MemProp.

(* ---------------------------------------------------------------------- *)
(** ** Concat *)

Lemma concat_nil :
  concat (@nil (list A)) = nil.
Proof using. auto. Qed.
Lemma concat_cons : forall l m,
  concat (l::m) = l ++ concat m.
Proof using. auto. Qed.
Lemma concat_one : forall l,
  concat (l::nil) = l.
Proof using.
  intros. rewrite concat_cons. rewrite concat_nil.
  rewrite~ app_nil_r.
Qed.
Lemma concat_app : forall m1 m2 : list (list A),
  concat (m1 ++ m2) = concat m1 ++ concat m2.
Proof using.
  induction m1; intros.
  rewrite concat_nil. do 2 rewrite~ app_nil_l.
  rewrite app_cons. do 2 rewrite concat_cons.
   rewrite app_assoc. fequals.
Qed.
Lemma concat_last : forall l m,
  concat (m & l) = concat m ++ l.
Proof using. intros. rewrite~ concat_app. rewrite~ concat_one. Qed.

Lemma concat_mem : forall Ls x,
  mem x (concat Ls) <->
  exists L,
    mem L Ls /\ mem x L.
Proof using.
  introv. induction Ls.
   simpl. iff I; inverts* I.
  rewrite concat_cons. iff I.
   rewrite mem_app in I. rew_refl in *. inverts I as I.
    exists a. splits~. simpl. rew_refl*.
    apply IHLs in I. lets (l&Il&Ix): (rm I).
     exists l. splits~. simpl. rew_refl*.
   rewrite mem_app. rew_refl. lets (l&Il&Ix): (rm I).
    simpl in Il. rew_refl in Il. inverts Il as Il.
     left~.
     right~. apply* IHLs.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Map *)

Section MapProp.
Variable B : Type.
Variable f : A -> B.
Lemma map_nil :
  map f nil = nil.
Proof using. auto. Qed.
Lemma map_cons : forall x l,
  map f (x::l) = f x :: map f l.
Proof using. auto. Qed.
Lemma map_app : forall l1 l2,
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof using.
  intros. unfold map.
  assert (forall accu,
    fold_right (fun x acc => f x :: acc) accu (l1 ++ l2) =
    fold_right (fun x acc => f x :: acc) nil l1 ++
     fold_right (fun x acc => f x :: acc) nil l2 ++ accu).
  induction l1; intros; simpl.
   do 2 rewrite app_nil_l. gen accu.
   induction l2; intros; simpl.
     auto.
     rewrite IHl2. rewrite~ app_cons.
   rewrite IHl1. rewrite~ app_cons.
  specializes H (@nil B). rewrite~ app_nil_r in H.
Qed.
Lemma map_last : forall x l,
  map f (l & x) = map f l & f x.
Proof using. intros. rewrite~ map_app. Qed.
Lemma length_map : forall l,
  length (map f l) = length l.
Proof using.
  induction l. auto.
  rewrite map_cons. do 2 rewrite length_cons. auto.
Qed.

Lemma nil_map : forall l,
  map f l = nil -> l = nil.
Proof using. introv E. apply length_zero_inv. rewrite <- length_map. rewrite~ E. Qed.

Lemma map_inj : forall l1 l2,
  (forall x y, f x = f y -> x = y) ->
  map f l1 = map f l2 ->
  l1 = l2.
Proof using.
  introv inj E. gen l2. induction l1; introv E.
   rewrite map_nil in E. symmetry in E. forwards~: nil_map E.
   destruct l2 as [|e l2]; tryfalse. repeat rewrite map_cons in E.
    inverts E as E1 E2. forwards: inj E1. substs. fequals~.
Qed.

Lemma map_mem : forall l (x : B),
  mem x (map f l) <->
    exists y, mem y l /\ x = f y.
Proof using.
  induction l; introv.
   simpl. iff I; false*. inverts* I.
   rewrite map_cons. iff I.
    simpl in I. rew_refl in I. inverts I as I.
     exists a. splits~. simpl. rew_refl. left~.
     apply IHl in I. lets (y&Iy&E): (rm I). exists y. splits~.
      simpl. rew_refl. right~.
    lets (y&Iy&E): (rm I). substs. simpls. rew_refl in *.
     inverts Iy as I. left~.
     right. apply IHl. exists~ y.
Qed.

End MapProp.

Lemma map_id : forall l,
  map id l = l.
Proof using. introv. induction~ l. rewrite map_cons. fequals~. Qed.


(* ---------------------------------------------------------------------- *)
(** ** Filter *)

Section FilterProp.
Variable f : A -> bool.
Lemma filter_nil :
  filter f nil = nil.
Proof using. auto. Qed.

Lemma filter_cons : forall x l,
  filter f (x::l) = if f x then x :: filter f l else filter f l.
Proof using. auto. Qed.

Lemma filter_app : forall l1 l2,
  filter f (l1 ++ l2) = filter f l1 ++ filter f l2.
Proof using.  (* todo: factorise with map_app *)
  intros. unfold filter.
  assert (forall accu,
    fold_right (fun x acc => if f x then x::acc else acc) accu (l1 ++ l2) =
    fold_right (fun x acc => if f x then x::acc else acc) nil l1 ++
     fold_right (fun x acc => if f x then x::acc else acc) nil l2 ++ accu).
  induction l1; intros; simpl.
   do 2 rewrite app_nil_l. gen accu.
   induction l2; intros; simpl.
     auto.
     case_if. fequals. rewrite IHl2. rewrite~ app_cons. fequals.
     case_if. fequals. rewrite IHl1. rewrite~ app_cons. apply IHl1.
  specializes H (@nil A). rewrite~ app_nil_r in H.
Qed.

Lemma filter_last : forall x l,
  filter f (l & x) = filter f l ++ (if f x then x::nil else nil).
Proof using. intros. rewrite~ filter_app. Qed.

Lemma Forall_filter_same : forall l,
  Forall f (filter f l).
Proof using.
  introv. induction l.
   rewrite filter_nil. constructors~.
   rewrite filter_cons. cases_if~.
Qed.

Lemma filter_mem_eq : forall l a,
  mem a (filter f l) = (mem a l && f a).
Proof using.
  introv. extens. induction l.
   rewrite filter_nil. iff I; false I.
   rewrite filter_cons. cases_if; iff I.
    simpls. rew_refl in *. inverts I as I; splits*.
    lets (I'&D): (rm I). simpls. rew_refl in *. inverts* I'.
    rewrite IHl in I. splits*. simpl. rew_refl. right*.
    lets (I'&D): (rm I). simpls. rew_refl in *. inverts* I'. false*.
Qed.

End FilterProp.

(* ---------------------------------------------------------------------- *)
(** ** Drop *)

Lemma drop_struct : forall n l,
  n <= length l -> exists l',
  length l' = n /\ l = l' ++ (drop n l).
Proof using.
  induction n; introv Len.
    exists~ (@nil A).
    destruct l. rewrite length_nil in Len. math.
     destruct (IHn l) as [l' [Le Eq]].
      rewrite length_cons in Len. math.
     exists (a::l'). split. rewrite length_cons. rewrite~ Le.
     rewrite app_cons. simpl. fequals~.
Qed.
(* todo: missing properties of drop *)


(* ---------------------------------------------------------------------- *)
(** ** Take *)

Lemma take_nil : forall l,
  take 0 l = nil.
Proof using. auto. Qed.

Lemma take_cons : forall x l n,
  take (S n) (x::l) = x :: (take n l).
Proof using. auto. Qed.

Lemma take_cons_pred : forall x l n,
  (n > 0) ->
  take n (x::l) = x :: (take (n-1) l).
Proof using.
  introv H. destruct n. false; math.
  simpl. fequals_rec. math.
Qed.

Lemma take_app_l : forall n l l',
  (n <= length l) ->
  take n (l ++ l') = take n l.
Proof using.
  induction n; destruct l; introv H;
   try rewrite length_nil in H;
   try rewrite length_cons in H; auto.
  math.
  rewrite app_cons. do 2 rewrite take_cons. fequals.
   applys IHn. math.
Qed.

Lemma take_app_r : forall n l l',
  (n >= length l) ->
  take n (l ++ l') = l ++ take (n - length l) l'.
Proof using.
  intros. gen n. induction l; introv H.
  rewrite length_nil in *. do 2 rewrite app_nil_l.
   fequals. math.
  rewrite length_cons in *. destruct n as [|n'].
    false. math.
    do 2 rewrite app_cons. rewrite take_cons.
    fequals. applys IHl. math.
Qed.

Lemma take_app_length : forall l l',
  take (length l) (l ++ l') = l.
Proof using.
  intros. rewrite take_app_r.
  asserts_rewrite (forall a, a - a = 0). math.
  rewrite take_nil. apply app_nil_r. math.
Qed.

Lemma take_at_length : forall l,
  take (length l) l = l.
Proof using.
  intros. lets: (@take_app_length l nil).
  rewrite~ app_nil_r in H.
Qed.

  (* todo: or name as take_length ? *)
Lemma length_take : forall n l,
  n <= length l ->
  length (take n l) = n.
Proof using.
  induction n; introv H.
  rewrite~ take_nil.
  destruct l. rewrite length_nil in H. math.
  rewrite take_cons.
   rewrite length_cons in *. rewrite IHn; math.
Qed.

Lemma take_struct : forall n l,
  n <= length l ->
  exists l', length (take n l) = n
          /\ l = (take n l) ++ l'.
Proof using. (* todo: relate with drop ! *)
  induction n; introv Len.
    exists~ l.
    destruct l. rewrite length_nil in Len. math. simpl.
     destruct (IHn l) as [l' [Le Eq]].
      rewrite length_cons in Len. math.
     exists l'. split. rewrite length_cons. rewrite~ Le.
     rewrite app_cons. fequals~.
Qed.

Lemma split_cons : forall {A1 A2}
 (l1:list A1) (l2:list A2) (x1:A1) (x2:A2) (l:list (A1*A2)),
  (l1,l2) = split l ->
  split ((x1,x2)::l) = (x1::l1,x2::l2).
Proof using.
  intros. destruct l; inverts H; simpl.
    auto.
    destruct p. simpl. destruct (split l). fequals.
Qed.

Lemma take_and_drop : forall n l f r,
  f = take n l -> r = drop n l -> n <= length l ->
  l = f ++ r /\ length f = n /\ length r = length l - n.
Proof using.
  induction n; introv F R L; simpls.
  subst. splits~. math.
  destruct l.
    rewrite length_nil in L. math.
    rewrite length_cons in L.
     forwards~ (F'&R'&L'): (>> IHn l (take n l) r). math.
     subst f. splits.
       rewrite app_cons. fequals.
       rewrite length_cons. math.
       rewrite length_cons. math.
Qed.

End OperationProperties.


(* This lemma requires [rev_cons] to be parameterised to be proven,
  this putting it out of the section. *)
Lemma map_rev : forall A B (f : A -> B) l,
  map f (rev l) = rev (map f l).
Proof using.
  induction l.
   reflexivity.
   rewrite map_cons. rewrite rev_cons. rewrite map_last. rewrite rev_cons. rewrite~ IHl.
Qed.


Implicit Arguments length_zero_inv [A l].
Implicit Arguments take_struct [A].


Module TakeInt. (* TODO: move to LibListZ *)
Import LibInt.
Section Facts.
Variables (A:Type).
Implicit Types x : A.
Implicit Types l : list A.

Lemma take_cons_pred_int : forall x l (n:int),
  n > 0 ->
  take (abs n) (x::l) = x :: (take (abs (n-1)) l).
Proof using. (* using stdlib *)
  introv Pos. rewrite take_cons_pred.
  rewrite abs_minus; try math. auto.
  forwards: Zabs_nat_lt 0 n; math.
Qed.

Lemma take_cons_int : forall x l (n:int),
  n >= 0 ->
  take (abs (n+1)) (x::l) = x :: (take (abs n) l).
Proof using.
  introv Pos. rewrite~ abs_plus.
  rewrite~ plus_comm. math.
Qed.

End Facts.
End TakeInt.
Export TakeInt.


(* ---------------------------------------------------------------------- *)
(** ** TakeDropLast *)

Section TakeDropLastProperties.
Context (A:Type) (IA:Inhab A).
Implicit Types x : A.
Implicit Types l : list A.

Lemma take_drop_last_spec : forall (x:A) (l l': list A),
  (l',x) = take_drop_last l -> l <> nil ->
  l = l' & x.
Proof using.
  induction l as [|a t]; introv E N. false.
  unfold take_drop_last in E. fold take_drop_last in E.
  destruct (take_drop_last t) as [u r].
   destruct t; inverts E. rewrite* app_nil_l.
   rewrite app_cons. fequals. applys IHt; auto_false*.
Qed.

Lemma take_drop_last_length : forall l l' x,
  (l',x) = take_drop_last l -> l <> nil ->
  length l' = length l - 1.
Proof using.
  (* TODO: simplify using lemma above *)
  intros l. induction l as [|x t]; introv E N.
  false.
  unfold take_drop_last in E. fold take_drop_last in E.
   sets_eq F: take_drop_last. destruct t as [|y u].
     inverts E. rewrite length_cons. math.
     destruct (F (y::u)) as [r v]. inverts E.
     forwards*: IHt. auto_false.
      rewrite length_cons in H. repeat rewrite length_cons.
      math.
Qed.

End TakeDropLastProperties.

Implicit Arguments take_drop_last_spec [[IA]].
Implicit Arguments take_drop_last_length [[IA]].


(* ---------------------------------------------------------------------- *)
(** ** NthDef *)

Section NthDefProperties.
Variables (A:Type).
Implicit Types n : nat.
Implicit Types d x : A.
Implicit Types l : list A.

Lemma nth_def_nil : forall n d,
  nth_def d n nil = d.
Proof using. introv. destruct~ n. Qed.

Lemma nth_def_zero : forall x l d,
  nth_def d 0 (x::l) = x.
Proof using. introv. reflexivity. Qed.

Lemma nth_def_succ : forall n x l d,
  nth_def d (S n) (x::l) = nth_def d n l.
Proof using. introv. reflexivity. Qed.

End NthDefProperties.


(* ---------------------------------------------------------------------- *)
(** ** Nth *)

Section nthProperties.
Variables (A:Type) (IA: Inhab A).
Implicit Types n : nat.
Implicit Types x : A.
Implicit Types l : list A.

Lemma nth_zero : forall x l,
  nth 0 (x::l) = x.
Proof using. intros. apply nth_def_zero. Qed.

Lemma nth_succ : forall n x l,
  nth (S n) (x::l) = nth n l.
Proof using. intros. apply nth_def_succ. Qed.

End nthProperties.

Implicit Arguments nth_zero [A [IA]].
Implicit Arguments nth_succ [A [IA]].


(* ---------------------------------------------------------------------- *)
(** * Update *)

Lemma length_update : forall A (l:list A) (i:nat) (v:A),
  length (update i v l) = length l.
Proof using.
  intros. gen i. induction l; intros.
  simple~.
  destruct i as [|i'].
    simpl. do 2 rewrite length_cons. auto.
    simpl. do 2 rewrite length_cons. rewrite~ IHl.
Qed.

Lemma nth_update_eq : forall `{Inhab A} (l:list A) (i:nat) (v:A),
  (i < length l)%nat ->
  nth i (update i v l) = v.
Proof using.
  introv N. gen l. induction i; intros.
  destruct l.
    simpl in N. rewrite length_nil in N. math.
    simple~.
  destruct l.
    simpl in N. rewrite length_nil in N. math.
    simpl. rewrite nth_succ. rewrite~ IHi. rewrite length_cons in N. math.
Qed.

Lemma nth_update_neq : forall `{Inhab A} (l:list A) (i j:nat) (v:A),
  (j < length l)%nat -> (i <> j) ->
  nth j (update i v l) = nth j l.
Proof using.
  introv. gen l i. induction j; introv B N.
  destruct i.
    false.
    destruct l. rewrite length_nil in B. math. simple~.
  destruct l. rewrite length_nil in B. math. destruct i.
    simpl. do 2 rewrite nth_succ. auto.
    simpl. do 2 rewrite nth_succ. apply~ IHj. rewrite length_cons in B. math.
Qed.

Lemma update_app_right:
  forall A ys j xs i ij (v : A),
  i = length xs ->
  ij = i + j ->
  update ij v (xs ++ ys) = xs ++ update j v ys.
Proof.
  induction xs as [| x xs ]; intros.
  { repeat rewrite app_nil_l.
    rewrite length_nil in *. replace ij with j by math.
    reflexivity. }
  { rewrite length_cons in *.
    repeat rewrite app_cons.
    replace ij with (1 + (length xs + j)) by math. simpl.
    erewrite (IHxs (i - 1)) by math.
    reflexivity. }
Qed.

Lemma update_app_right_here:
  forall A i (xs ys : list A) x y,
  i = length xs ->
  update i x (xs ++ y :: ys) = xs & x ++ ys.
Proof.
  intros.
  rewrite app_assoc.
  erewrite update_app_right with (j := 0) by eauto.
  reflexivity. (* !? *)
Qed.

(* ---------------------------------------------------------------------- *)
(** * Make *)

Lemma nth_make : forall `{Inhab A} (i n:nat) (v:A),
  (i < n)%nat -> nth i (make n v) = v.
Proof using.
  introv. gen n; induction i; introv E.
  destruct n. math. auto.
  destruct n. math. simpl. rewrite nth_succ. rewrite~ IHi. math.
Qed.

Lemma length_make : forall A (n:nat) (v:A),
  length (make n v) = n.
Proof using.
  intros. induction n.
  auto.
  simpl. rewrite length_cons. math.
Qed.

Lemma cons_make: forall n A (x : A),
  0 < n ->
  x :: make (n - 1) x = make n x.
Proof.
  induction n; intros; simpl.
  { math. }
  { rewrite <- minus_n_O. eauto. }
Qed.

(* ---------------------------------------------------------------------- *)
(** * Fold *)

Section Fold.
Variables (A B:Type) (m:monoid_def B) (L:list A) (f:A->B).
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

(* See also [fold_pointwise], stated later on because it depends on [Mem]. *)

(* ********************************************************************** *)
(** * Association lists *)

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

Implicit Arguments assoc [[A] [B] [IB] [CA]].
Implicit Arguments mem_assoc [[A] [B]].
Implicit Arguments keys [[A] [B]].
Implicit Arguments remove_assoc [[A] [B] [CA]].


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
  simpl. rew_refl. cases_if.
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
   do 2 unfolds in I. simpls. rew_refl in *. inverts I as I.
    right. apply~ IHl.
    left~.
   rewrite map_cons in I. do 2 unfolds. simpls. rew_refl in *. inverts I as I.
    right~.
    left. apply~ IHl.
Qed.

Lemma mem_assoc_cons : forall A B (l : list (A * B)) a e,
  mem_assoc a (e :: l) = (a '= fst e) || mem_assoc a l.
Proof using.
  introv. extens. iff M.
   do 2 unfolds in M. simpl in M. rew_refl. rew_refl* in M.
   rew_refl in M. inverts M as M.
    destruct e as [a b]. do 2 unfolds. simpl. rew_refl*.
    do 2 unfolds. simpl. rew_refl*.
Qed.

Lemma mem_assoc_nil : forall A B a,
  mem_assoc a (nil : list (A * B)) = false.
Proof using. autos*. Qed.

Lemma mem_mem_assoc : forall A B (l : list (A * B)) a b,
  mem (a, b) l ->
  mem_assoc a l.
Proof using.
  introv I. induction~ l. simpl in I. rewrite mem_assoc_cons. rew_refl in *. inverts* I.
Qed.

Lemma assoc_eq_mem_assoc : forall A B `{Inhab B} `{Comparable A} (l : list (A * B)) a,
  mem (a, assoc a l) l = mem_assoc a l.
Proof using.
  introv. induction l as [|[a' b'] l].
   reflexivity.
   simpl. extens. case_if; iff I; rewrite mem_assoc_cons in *; rew_refl in *.
    repeat inverts I as I.
     autos~.
     rewrite* <- IHl.
    inverts I; substs*.
    rew_refl in I. inverts I; tryfalse. right. rewrite~ <- IHl.
    rew_refl. inverts I; tryfalse~. right. rewrite~ IHl.
Qed.

Lemma mem_assoc_exists_mem : forall A B (l : list (A * B)) a,
  mem_assoc a l ->
  exists b, mem (a, b) l.
Proof using.
  introv M. induction l as [|[a' b'] l]; tryfalse.
  do 2 unfolds in M. simpl in M. rew_refl in M. inverts M as M.
   forwards (b&M'): (rm IHl) (rm M). exists b. simpl. rew_refl*.
   exists b'. simpl. rew_refl*.
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




(* ********************************************************************** *)
(* * Tactics for rewriting *)

Hint Rewrite app_cons app_nil_l app_nil_r app_assoc
 app_cons_one : rew_app. (* app_last *)
Hint Rewrite fold_right_nil fold_right_cons fold_right_app
 fold_right_last : rew_foldr.
Hint Rewrite fold_left_nil fold_left_cons fold_left_app
 fold_left_last : rew_foldl.
Hint Rewrite length_nil length_cons length_app
 length_last length_rev : rew_length.
Hint Rewrite rev_nil rev_app rev_cons rev_last rev_rev : rew_rev.
 (* +rev_cons_app *)
Hint Rewrite concat_nil concat_app concat_cons concat_last : rew_concat.
Hint Rewrite map_nil map_cons map_app map_last : rew_map.
Hint Rewrite mem_nil mem_cons mem_app mem_last
 mem_cons_eq mem_last_eq : rew_mem.
Hint Rewrite keys_nil keys_cons keys_app keys_last : rew_keys.
Hint Rewrite assoc_cons assoc_here : rew_assoc.

(* TODO: rew_tactics other than [rew_app] and [rew_length]
   will become deprecated; use [rew_list] instead. *)

Tactic Notation "rew_app" :=
  autorewrite with rew_app.
Tactic Notation "rew_foldr" :=
  autorewrite with rew_foldr rew_app.
Tactic Notation "rew_foldl" :=
  autorewrite with rew_foldl rew_app.
Tactic Notation "rew_length" :=
  autorewrite with rew_length.
Tactic Notation "rew_rev" :=
  autorewrite with rew_rev rew_app.
Tactic Notation "rew_concat" :=
  autorewrite with rew_concat rew_app.
Tactic Notation "rew_map" :=
  autorewrite with rew_map rew_app.
Tactic Notation "rew_mem" :=
  autorewrite with rew_mem rew_app.
Tactic Notation "rew_keys" :=
  autorewrite with rew_keys rew_app.
Tactic Notation "rew_assoc" :=
  autorewrite with rew_assoc rew_app.

Tactic Notation "rew_app" "in" hyp(H) :=
  autorewrite with rew_app in H.
Tactic Notation "rew_foldr" "in" hyp(H) :=
  autorewrite with rew_foldr rew_app in H.
Tactic Notation "rew_foldl" "in" hyp(H) :=
  autorewrite with rew_foldl rew_app in H.
Tactic Notation "rew_length" "in" hyp(H) :=
  autorewrite with rew_length in H.
Tactic Notation "rew_rev" "in" hyp(H) :=
  autorewrite with rew_rev rew_app in H.
Tactic Notation "rew_concat" "in" hyp(H) :=
  autorewrite with rew_concat rew_app in H.
Tactic Notation "rew_map" "in" hyp(H) :=
  autorewrite with rew_map rew_app in H.
Tactic Notation "rew_mem" "in" hyp(H) :=
  autorewrite with rew_mem rew_app in H.
Tactic Notation "rew_keys" "in" hyp(H) :=
  autorewrite with rew_keys rew_app in H.
Tactic Notation "rew_assoc" "in" hyp(H) :=
  autorewrite with rew_assoc rew_app in H.

Tactic Notation "rew_app" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_app).
  (* autorewrite with rew_app in *. *)

  (* TODO: if those are kept, need the efficiency workaround *)
Tactic Notation "rew_foldr" "in" "*" :=
  autorewrite with rew_foldr rew_app in *.
Tactic Notation "rew_foldl" "in" "*" :=
  autorewrite with rew_foldl rew_app in *.
Tactic Notation "rew_length" "in" "*" :=
  autorewrite with rew_length in *.
Tactic Notation "rew_rev" "in" "*" :=
  autorewrite with rew_rev rew_app in *.
Tactic Notation "rew_concat" "in" "*" :=
  autorewrite with rew_concat rew_app in *.
Tactic Notation "rew_map" "in" "*" :=
  autorewrite with rew_map rew_app in *.
Tactic Notation "rew_mem" "in" "*" :=
  autorewrite with rew_mem rew_app in *.
Tactic Notation "rew_keys" "in" "*" :=
  autorewrite with rew_keys rew_app in *.
Tactic Notation "rew_assoc" "in" "*" :=
  autorewrite with rew_assoc rew_app in *.

Tactic Notation "rew_app" "~" :=
  rew_app; auto_tilde.
Tactic Notation "rew_rev" "~" :=
  rew_rev; auto_tilde.
Tactic Notation "rew_mem" "~" :=
  rew_mem; auto_tilde.
Tactic Notation "rew_length" "~" :=
  rew_length; auto_tilde.

Hint Rewrite app_cons app_nil_l app_nil_r app_assoc
 app_cons_one
 fold_right_nil fold_right_cons fold_right_app
 fold_right_last
 fold_left_nil fold_left_cons fold_left_app
 fold_left_last
 length_nil length_cons length_app length_rev
 length_last
 rev_nil rev_app rev_cons rev_last rev_rev
 concat_nil concat_app concat_cons concat_last
  map_nil map_cons map_app map_last : rew_list.

Hint Rewrite app_cons app_nil_l app_nil_r app_assoc
 app_cons_one
 mem_nil mem_cons mem_app mem_last
 mem_cons_eq mem_last_eq
 keys_nil keys_cons keys_app keys_last
 assoc_cons assoc_here : rew_lists.

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

Tactic Notation "rew_lists" :=
  autorewrite with rew_lists.
Tactic Notation "rew_lists" "~" :=
  rew_lists; auto_tilde.
Tactic Notation "rew_lists" "*" :=
  rew_lists; auto_star.
Tactic Notation "rew_lists" "in" "*" :=
  autorewrite with rew_lists in *.
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
(** * Other definitions and results *)

(* ---------------------------------------------------------------------- *)
(** * TODO *)

(* todo *)

Definition is_head A (l:list A) (x:A) :=
  exists t, l = x::t.

Definition is_tail A (l:list A) (t:list A) :=
  exists x, l = x::t.

Definition is_last A (l:list A) (x:A) :=
  exists t, l = t&x.

Definition is_init A (l:list A) (t:list A) :=
  exists x, l = t&x.

Hint Unfold is_head is_tail is_last is_init.

Section IsProp.
Variables A : Type.
Implicit Types x : A.

Lemma is_last_one : forall x,
  is_last (x::nil) x.
Proof using. intros. unfolds. exists~ (@nil A). Qed.

Lemma is_init_one : forall x,
  is_init (x::nil) nil.
Proof using. intros. unfolds. exists~ x. Qed.

End IsProp.

Hint Immediate is_last_one.
Hint Immediate is_init_one.


(* ---------------------------------------------------------------------- *)
(** * Inversions on the structure of lists *)

Section Inversions.
Variables A : Type.
Implicit Types l : list A.

Lemma cons_neq_nil : forall x l,
  x::l <> nil.
Proof using. auto_false. Qed.

Lemma last_eq_nil_inv : forall a l,
  l & a = nil -> False.
Proof using. induction l; rew_app; intros; false. Qed.

Lemma nil_eq_last_inv : forall a l,
  nil = l & a -> False.
Proof using. intros. apply* last_eq_nil_inv. Qed.

Lemma rev_eq_nil_inv : forall l,
  rev l = nil -> l = nil.
Proof using.
  destruct l; rew_rev; intros. auto.
  false* last_eq_nil_inv.
Qed.

Lemma nil_eq_rev_inv : forall l,
  nil = rev l -> l = nil.
Proof using. introv H. apply~ rev_eq_nil_inv. Qed.

Lemma app_eq_nil_inv : forall l1 l2,
  l1 ++ l2 = nil -> l1 = nil /\ l2 = nil.
Proof using. destruct l1; destruct l2; intros; tryfalse~; auto. Qed.

Lemma nil_eq_app_inv : forall l1 l2,
  nil = l1 ++ l2 -> l1 = nil /\ l2 = nil.
Proof using. intros. symmetry in H. apply* app_eq_nil_inv. Qed.

Lemma app_eq_self_inv_r : forall l1 l2,
  l2 = l1 ++ l2 -> l1 = nil.
Proof using.
  introv E. apply length_zero_inv.
  lets: (func_eq_1 length E). rew_length in H. math.
Qed.

Lemma app_eq_self_inv_l : forall l1 l2,
  l1 = l1 ++ l2 -> l2 = nil.
Proof using.
  introv E. apply length_zero_inv.
  lets: (func_eq_1 length E). rew_length in H. math.
Qed.

Lemma app_rev_eq_nil_inv : forall l1 l2,
  l1 ++ rev l2 = nil -> l1 = nil /\ l2 = nil.
Proof using.
  intros. lets H1 H2: (app_eq_nil_inv _ _ H).
  applys_to H2 rev_eq_nil_inv. autos*.
Qed.

Lemma nil_eq_app_rev_inv : forall l1 l2,
  nil = l1 ++ rev l2 -> l1 = nil /\ l2 = nil.
Proof using. intros. apply* app_rev_eq_nil_inv. Qed.

(* todo: too specific? *)

Lemma nil_eq_last_val_app_inv : forall x l1 l2,
  nil = l1 & x ++ l2 -> False.
Proof using. intros. destruct l1; inverts H. Qed.

Lemma last_eq_last_inv : forall x1 x2 l1 l2,
  l1 & x1 = l2 & x2 -> l1 = l2 /\ x1 = x2.
Proof using.
  introv H. gen l2. induction l1; introv E; rew_app in E.
  destruct l2; rew_app in E; inverts E as E.
   auto. false nil_eq_last_inv E.
  destruct l2; rew_app in E.
    inverts E as E. false last_eq_nil_inv E.
    inverts E. forwards* [? ?]: IHl1.
     split; congruence. (* TODO: congruence that does split *)
Qed.

Lemma cons_eq_last_val_app_inv : forall x y l1 l2 l,
  x :: l = l1 & y ++ l2 ->
  (l1 = nil /\ x = y /\ l = l2) \/ (exists l1', l1 = x::l1').
Proof using.
  intros. destruct l1; rew_list in H; inverts H.
   left~. right*.
Qed.

Lemma app_eq_prefix_inv_l : forall l1 l2 l2',
  l1 ++ l2 = l1 ++ l2' -> l2 = l2'.
Proof using.
  introv E. induction l1; rew_list in *. auto. inverts* E.
Qed.

Lemma last_inv : forall l, (* TODO: rename to last_inv_pos_length *)
  (length l > 0%nat) ->
  exists x l', l = l' & x.
Proof using.
  induction l; rew_length; introv H.
  false. math.
  destruct l.
    exists~ a (@nil A).
    destruct IHl as (x&l'&E). rew_length in *. math.
    exists x (a::l'). rewrite~ E.
Qed.

Lemma last_case : forall l,
  l = nil \/ exists x l', l = l' & x.
Proof using.
  intros. destruct l. left*. right.
  forwards* (x&l'&H): (last_inv (a::l)).
    rew_length. math.
Qed.

Lemma last_neq_nil : forall l,
  l <> nil -> exists x q, l = q&x.
Proof using. introv N. destruct* (@last_case l). Qed.

Lemma app_not_empty_l : forall l1 l2,
  l1 <> nil -> l1 ++ l2 <> nil.
Proof using. introv NE K. apply NE. destruct~ (app_eq_nil_inv _ _ K). Qed.

Lemma app_not_empty_r : forall l1 l2,
  l2 <> nil -> l1 ++ l2 <> nil.
Proof using. introv NE K. apply NE. destruct~ (app_eq_nil_inv _ _ K). Qed.

Lemma length_zero_iff_nil : forall l,
  length l = 0 <-> l = nil.
Proof using.
  intros. iff M. destruct l; simpls; auto_false*. subst*. Qed.

Lemma length_neq_elim : forall l1 l2,
  length l1 <> length l2 -> (l1 <> l2).
Proof using. introv N E. subst. auto. Qed.

Lemma concat_eq_nil : forall L (l : list A),
  concat L = nil ->
  mem l L ->
  l = nil.
Proof using.
  induction L; introv E I; inverts I as I.
  rewrite concat_cons in E. fold_bool. rew_refl in I.
  forwards (?&C): app_eq_nil_inv (rm E). substs. inverts~ I.
Qed.

Lemma nil_mem : forall l,
  (forall x : A, ~ mem x l) ->
  l = nil.
Proof using. introv P. destruct~ l. false P. simpl. rew_refl*. Qed.

End Inversions.

Implicit Arguments last_eq_nil_inv [A a l].
Implicit Arguments nil_eq_last_inv [A a l].
Implicit Arguments rev_eq_nil_inv [A l].
Implicit Arguments nil_eq_rev_inv [A l].
Implicit Arguments app_eq_nil_inv [A l1 l2].
Implicit Arguments nil_eq_app_inv [A l1 l2].
Implicit Arguments app_rev_eq_nil_inv [A l1 l2].
Implicit Arguments nil_eq_app_rev_inv [A l1 l2].
Implicit Arguments nil_eq_last_val_app_inv [A x l1 l2].
Implicit Arguments cons_eq_last_val_app_inv [A x y l1 l2 l].


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
(* ********************************************************************** *)
(* ********************************************************************** *)
(** * Logical predicates *)

Section LogicList.

(** [Forall P L] asserts that all the elements in the list [L]
    satisfy the predicate [P]. *)

Inductive Forall A (P : A -> Prop)
  : list A -> Prop :=
  | Forall_nil :
      Forall P nil
  | Forall_cons : forall l x,
      P x -> Forall P l ->
      Forall P (x::l).

(** [Forall2 P L1 L2] asserts that the lists [L1] and [L2]
    have the same length and that elements at corresponding
    indices are related by the binary relation [P]. *)

Inductive Forall2 A B (P : A -> B -> Prop)
  : list A -> list B -> Prop :=
  | Forall2_nil :
      Forall2 P nil nil
  | Forall2_cons : forall l1 l2 x1 x2,
      P x1 x2 -> Forall2 P l1 l2 ->
      Forall2 P (x1::l1) (x2::l2).

(** Similar to [Forall2] except that it relates three lists *)

Inductive Forall3 A B C (P : A -> B -> C -> Prop)
  : list A -> list B -> list C -> Prop :=
  | Forall3_nil :
      Forall3 P nil nil nil
  | Forall3_cons : forall l1 l2 l3 x1 x2 x3,
      P x1 x2 x3 -> Forall3 P l1 l2 l3 ->
      Forall3 P (x1::l1) (x2::l2) (x3::l3).

(** [exists P L] asserts that there exists a value in the
    list [L] that satisfied the predicate [P]. *)

Inductive Exists A (P : A -> Prop)
  : list A -> Prop :=
  | Exists_here : forall l x,
      P x -> Exists P (x::l)
  | Exists_next : forall l x,
      Exists P l ->
      Exists P (x::l).

(** [exists2 P L1 L2] asserts that there exists an index [n]
    such that the n-th element of [L1] and the n-th element
    of [L2] are related by the binary relation [P]. *)

Inductive Exists2 A1 A2 (P : A1 -> A2 -> Prop)
  : list A1 -> list A2 -> Prop :=
  | Exists2_here : forall l1 l2 x1 x2,
      P x1 x2 -> Exists2 P (x1::l1) (x2::l2)
  | Exists2_next : forall l1 l2 x1 x2,
      Exists2 P l1 l2 ->
      Exists2 P (x1::l1) (x2::l2).

(** [filter P L] produces a list [L'] that is the sublist of [L]
    made exactly of the elements of [L] that satisfy [P]. *)

Definition Filter A (P : A->Prop) :=
  fold_right (fun x acc => If P x then x::acc else acc) (@nil A).

(** [filters P L L'] asserts that [L'] is the sublist of [L]
    made exactly of the elements of [L] that satisfy [P]. *)
   (* DEPRECATED: use Filter instead *)

Inductive Filters A (P : A -> Prop)
  : list A -> list A -> Prop :=
  | Filters_nil : Filters P nil nil
  | Filters_cons_yes : forall l l' x,
      P x -> Filters P l l' ->
      Filters P (x::l) (x::l')
  | Filters_cons_no : forall l l' x,
      ~ (P x) -> Filters P l l' ->
      Filters P (x::l) l'.

(** [Mem x l] asserts that [x] belongs to [M] *)

Inductive Mem A (x:A) : list A -> Prop :=
  | Mem_here : forall l,
      Mem x (x::l)
  | Mem_next : forall y l,
      Mem x l ->
      Mem x (y::l).

(** [Remove_duplicates L] produces a list [L'] that is the sublist of [L]
    obtained by keeping only the first occurence of every item. *)

Fixpoint Remove_duplicates A (L:list A) :=
  match L with
  | nil => nil
  | x::L' => x :: (Filter (<> x) (Remove_duplicates L'))
  end.

(** [No_duplicates L] asserts that [L] does not contain any
    duplicated item. *)

Inductive No_duplicates A : list A -> Prop :=
  | No_duplicates_nil : No_duplicates nil
  | No_duplicates_cons : forall x l,
      ~ (Mem x l) -> No_duplicates l -> No_duplicates (x::l).

(** [Nth n L x] asserts that the n-th element of the list [L]
    exists and is exactly [x] *)

Inductive Nth A : nat -> list A -> A -> Prop :=
  | Nth_here : forall l x,
      Nth 0 (x::l) x
  | Nth_next : forall y n l x,
      Nth n l x ->
      Nth (S n) (y::l) x.

(** [Update n x L L'] asserts [L'] is the list obtained by substituting
    in [L] the item at index [n] with [x]. *)

Definition Update A (n:nat) (x:A) l l' :=
    length l' = length l
  /\ (forall y m, Nth m l y -> m <> n -> Nth m l' y)
  /\ Nth n l' x.

(** [Assoc x v l] asserts that [(x,v)] the first pair of the
    form [(x,_)] in [l] *)

Inductive Assoc A B (x:A) (v:B) : list (A*B) -> Prop :=
  | Assoc_here : forall l ,
      Assoc x v ((x,v)::l)
  | Assoc_next : forall y l (w:B),
      Assoc x v l -> x <> y ->
      Assoc x v ((y,w)::l).

(** [has pair x1 x2 l1 l2] asserts that there exists an
    index [n] such that the n-th element of [l1] is [x1]
    and the n-th element of [l2] is [x2] *)

Definition has_pair A1 A2 (x1:A1) (x2:A2) l1 l2 :=
  Exists2 (fun v1 v2 => v1 = x1 /\ v2 = x2) l1 l2.

Lemma has_pair_here : forall A1 A2 (x1:A1) (x2:A2) l1 l2,
  has_pair x1 x2 (x1::l1) (x2::l2).
Proof using. intros. constructor~. Qed.

Lemma has_pair_next : forall A1 A2 (x1:A1) (x2:A2) y1 y2 l1 l2,
  has_pair x1 x2 l1 l2 ->
  has_pair x1 x2 (y1::l1) (y2::l2).
Proof using. introv H. apply* Exists2_next. Qed.

End LogicList.



(* ********************************************************************** *)
(** * Properties of predicate on lists *)


(* ---------------------------------------------------------------------- *)
(* ** Forall *)

Section ForallProp.
Variables A : Type.
Implicit Types l : list A.

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
   introv IN. simpl in IN. rew_refl in IN.
    inverts IN; inverts~ I. apply~ IHl.
   constructors.
    apply I. simpl. rew_refl. left*.
    apply~ IHl. introv IN. apply~ I.
     simpl. rew_refl. right*.
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
    induction~ C. simpl. case_if~.
   rewrite~ isTrue_false. fold_bool.
    induction~ l.
     false C. constructor~.
     simpl. case_if~.
      apply~ IHl. intro F; apply C. constructor~.
      clear C IHl. induction* l.
Qed.


(* ---------------------------------------------------------------------- *)
(* ** Forall2 *)

Section PropProperties2.
Variables A1 A2 : Type.
Implicit Types l : list A1.
Implicit Types r : list A2.
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
(* ** Exists *)

Section ExistsProp.
Variables A : Type.
Implicit Types l : list A.

Lemma Exists_nil_inv : forall (P : A -> Prop),
  Exists P nil -> False.
Proof using. introv H. invert* H. Qed.

Lemma Exists_cons_inv : forall (P : A -> Prop) l x,
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

Lemma Exists_exists_st : forall (P : A -> bool) l,
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

Lemma Exists_weaken : forall (P Q : A -> Prop) l,
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
(* ** Nth *)

Section NthProperties.
Variables (A : Type) (IA : Inhab A).
Implicit Types l : list A.
Implicit Types x : A.
Implicit Types n : nat.
Hint Constructors Nth.

Lemma Nth_lt_length : forall n l x,
  Nth n l x -> n < length l.
Proof using.
  induction n; introv H; inverts H.
  rewrite length_cons. math.
  rewrite length_cons. simpl. rew_nat*.
Qed.

Lemma length_Nth_lt : forall A n (l : list A),
  n < length l -> exists x, Nth n l x.
Proof using.
  induction n; introv Comp; destruct l as [|a l'];
    rew_list in Comp; try solve [math].
   eexists. apply Nth_here.
   simpls. rewrite lt_SS in Comp.
    forwards (x&Hx): IHn Comp. exists x.
    apply* Nth_next.
Qed.

Lemma Nth_func: forall n l x1 x2,
  Nth n l x1 -> Nth n l x2 -> x1 = x2.
Proof using. introv H1. induction H1; intro H2; inverts~ H2. Qed.

Lemma Nth_to_nth_def : forall n l x dummy,
  Nth n l x -> nth_def dummy n l = x.
Proof using. introv H. induction~ H. Qed.

Lemma Nth_to_nth : forall n l x,
  Nth n l x -> nth n l = x.
Proof using. introv H. apply~ Nth_to_nth_def. Qed.

Lemma mem_Nth : forall l x,
  mem x l -> exists n, Nth n l x.
Proof using.
  intros. induction l.
  rewrite mem_nil in H. false.
  rewrite mem_cons in H. rew_reflect in H. destruct H.
   fold_prop. subst*.
   forwards* [n ?]: IHl.
Qed.

Implicit Arguments mem_Nth [l x].

Lemma mem_nth : forall l x,
  mem x l -> exists n, nth n l = x.
Proof using.
  intros. forwards [n P]: (mem_Nth H).
  exists n. apply~ Nth_to_nth.
Qed.

Lemma Nth_app_l : forall n x l1 l2,
  Nth n l1 x -> Nth n (l1 ++ l2) x.
Proof using. induction n; introv H; inverts H; rew_list*. Qed.

Lemma Nth_app_r : forall n m x l1 l2,
  Nth m l2 x -> n = (m + length l1)%nat -> Nth n (l1 ++ l2) x.
Proof using.
  intros. subst. gen m. induction l1; introv H.
  rew_list. applys_eq~ H 3.
  rew_list. applys_eq* Nth_next 3.
Qed.

Lemma Nth_app_inv : forall n x l1 l2,
  Nth n (l1++l2) x ->
     (Nth n l1 x)
  \/ (exists m, n = (length l1 + m)%nat /\ Nth m l2 x).
Proof using.
  introv. gen n. induction l1; introv H; rew_list in H.
  right. rew_length. exists~ n.
  inverts H. left~.
   forwards* M: IHl1. destruct M.
    left~. unpack. rew_length.
    right*. exists m. split~. math.
Qed.

Lemma Nth_nil_inv : forall n x,
  Nth n nil x -> False.
Proof using. introv H. inverts H. Qed.

Lemma Nth_cons_inv : forall n x l,
  Nth n l x ->
     (exists q, l = x::q /\ n = 0%nat)
  \/ (exists y q m, l = y::q /\ Nth m q x /\ n = (m+1)%nat).
Proof using.
  introv H. inverts H. left*.
  right. eauto 8 with maths.
Qed.

Lemma Nth_mem : forall l x n,
  Nth n l x -> mem x l.
Proof using. clear IA. introv N. induction N; simpl; rew_refl* in *. Qed.

Lemma nth_def_if_in_length : forall l d n v,
  n < length l ->
  nth_def d n l = v ->
  Nth n l v.
Proof using.
  introv I E. forwards (v'&Nv): length_Nth_lt I.
  erewrite Nth_to_nth_def in E; [| apply~ Nv ]. substs~.
Qed.

End NthProperties.

Lemma Forall2_Nth_nth_def : forall A B (P : A -> B -> Prop) la lb n v d,
  Forall2 P la lb ->
  Nth n la v ->
  Nth n lb (nth_def d n lb).
Proof using.
  introv F N. forwards L: Forall2_length F. forwards I: Nth_lt_length N.
  rewrite L in I. forwards*: nth_def_if_in_length I.
Qed.

(* ---------------------------------------------------------------------- *)
(* ** Mem *)

Section MemFacts.
Hint Constructors Mem.

Lemma Mem_induct : forall (A : Type) (x : A) (P : list A -> Prop),
  (forall l : list A, P (x :: l)) ->
  (forall (y : A) (l : list A), Mem x l -> x <> y -> P l -> P (y :: l)) ->
  (forall l : list A, Mem x l -> P l).
Proof using.
  introv HH HN M. induction l.
  inverts M.
  tests: (x = a). auto. inverts M; auto_false*.
Qed.

Lemma Mem_nil_eq : forall A (x:A),
  Mem x nil = False.
Proof using. intros. extens. iff H; inverts H. Qed.

Lemma Mem_cons_eq : forall A (x y:A) l,
  Mem x (y::l) = ((x = y) \/ (Mem x l)).
Proof using. intros. extens. iff H; inverts~ H. Qed.

Lemma Mem_app_or_eq : forall (A:Type) (l1 l2 : list A) x,
  Mem x (l1 ++ l2) = (Mem x l1 \/ Mem x l2).
Proof using.
  intros. extens. induction l1; rew_app.
  split. auto. introv [H|?]. inverts H. auto.
  iff M. inverts~ M. rewrite IHl1 in H0. destruct* H0.
   destruct M. inverts~ H. constructors. rewrite~ IHl1.
   constructors. rewrite~ IHl1.
Qed.

Lemma Mem_app_or : forall (A:Type) (l1 l2 : list A) x,
  Mem x l1 \/ Mem x l2 -> Mem x (l1 ++ l2).
Proof using. intros. rewrite~ Mem_app_or_eq. Qed.

Lemma Mem_last : forall A (L:list A) x,
  Mem x (L & x).
Proof using. intros. apply* Mem_app_or. Qed.

Lemma Mem_rev : forall A (L:list A) x,
  Mem x L -> Mem x (rev L).
Proof using. introv H. induction H; rew_rev; apply~ Mem_app_or. Qed.

Lemma Mem_rev_iff : forall A (L:list A) x,
  Mem x L <-> Mem x (rev L).
Proof using.
 iff M.
 apply~ Mem_rev.
 lets H: Mem_rev M. rewrite~ rev_rev in H.
Qed.

Lemma Mem_inv : forall A (L:list A) x y,
  Mem x (y::L) -> x = y \/ x <> y /\ Mem x L.
Proof using. introv H. tests: (x = y). eauto. inverts H. false. eauto. Qed.

Lemma Mem_map : forall (A B:Type) (f:A->B) (l: list A) x,
  Mem x l -> Mem (f x) (map f l).
Proof using. introv M. induction M; rew_map; auto. Qed.

Fixpoint mem_decide `{Comparable A} (x : A) (l : list A) :=
  match l with
  | nil => false
  | y::l' => ifb x = y then true else mem_decide x l'
  end.

Global Instance Mem_decidable : forall `{Comparable A} (x : A) (l : list A),
   Decidable (Mem x l).
Proof using.
  intros. applys decidable_make (mem_decide x l). extens. rew_refl.
  induction l; simpl.
  iff E. false. inverts E.
  case_if.
    iff E; subst*.
    iff E. constructors*. inverts* E.
Qed.

Lemma Mem_mem : forall A l (a:A),
  Mem a l = mem a l.
Proof using.
  introv. extens. induction l; iff I; inverts I as I;
    simpls; fold_bool; rew_refl in *; autos*.
   inverts* I.
Qed.

End MemFacts.


(* ---------------------------------------------------------------------- *)
(** ** FilterProp *)

Section FilterFacts.
Variables (A:Type).
Implicit Types P : A -> Prop.

Lemma Filter_nil : forall P,
  Filter P nil = nil.
Proof using. auto. Qed.

Lemma Filter_cons : forall x l P,
  Filter P (x::l) = If P x then x :: Filter P l else Filter P l.
Proof using. auto. Qed.

Lemma Filter_app : forall l1 l2 P,
  Filter P (l1 ++ l2) = Filter P l1 ++ Filter P l2.
Proof using.  (* todo: factorise with map_app and above *)
  intros. unfold Filter.
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

Lemma Filter_last : forall x l P,
  Filter P (l & x) = Filter P l ++ (If P x then x::nil else nil).
Proof using. intros. rewrite~ Filter_app. Qed.

Lemma Filter_neq : forall x (L:list A),
  ~ Mem x (Filter (<> x) L).
Proof using.
  intros. induction L.
  rewrite Filter_nil. introv M. inverts M.
  rewrite Filter_cons. case_if.
    introv M. inverts M; false.
    auto.
Qed.

Lemma Filter_Mem : forall x (L:list A) (P:A->Prop),
  Mem x L -> P x -> Mem x (Filter P L).
Proof using.
  Hint Constructors Mem.
  introv H Px. induction H using Mem_induct.
  rewrite Filter_cons. case_if*.
  rewrite Filter_cons. case_if*.
Qed.

Lemma Filter_Mem_inv : forall x (L:list A) P,
  Mem x (Filter P L) -> Mem x L /\ P x.
Proof using.
  Hint Constructors Mem.
  introv M. induction L.
  rewrite Filter_nil in M. inverts M.
  rewrite Filter_cons in M. case_if. inverts* M. autos*.
Qed.

Lemma Filter_length_le : forall (L:list A) P,
  (length (Filter P L) <= length L)%nat.
Proof using.
  intros. induction L.
  rewrite Filter_nil. math.
  rewrite Filter_cons. case_if; rew_length; math.
Qed.

Lemma Filter_eq_Mem_length : forall x (L:list A),
  Mem x L -> (length (Filter (= x) L) >= 1)%nat.
Proof using.
  introv M. induction L.
  inverts M.
  rewrite Filter_cons. case_if.
    rew_list. nat_math.
    inverts M. false. applys~ IHL.
Qed.

Lemma Filter_neq_Mem_length : forall x (L:list A),
  Mem x L -> (length (Filter (<> x) L) < length L)%nat.
Proof using.
  introv M. induction L.
  inverts M.
  rewrite Filter_cons. case_if.
    inverts M. false. rew_length. forwards~: IHL. math.
    lets: (Filter_length_le L (<> x)). rew_length. math.
Qed.

Lemma Filter_disjoint_predicates_length : forall (P Q:A-> Prop) L,
  (forall x, Mem x L -> P x -> Q x -> False) ->
  (length (Filter P L) + length (Filter Q L) <= length L)%nat.
Proof using.
  introv. induction L; introv H.
  rew_list. nat_math.
  specializes IHL. intros. applys* H x.
  repeat rewrite Filter_cons. do 2 case_if; rew_list.
    false* H.
    nat_math.
    nat_math.
    nat_math.
Qed.

Lemma Filter_negated_predicates_length : forall (P:A-> Prop) L,
  length (Filter (fun x => P x) L) + length (Filter (fun x => ~ P x) L) <= length L.
Proof using.
  intros. applys~ Filter_disjoint_predicates_length P (fun x => ~ P x) L.
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

End FilterFacts.


(* ---------------------------------------------------------------------- *)
(* ** No_duplicates *)

  (* TODO: complete with a few potential missing lemmas *)

Lemma No_duplicates_app : forall A (L1 L2 : list A),
  No_duplicates L1 ->
  No_duplicates L2 ->
  (forall x, Mem x L1 -> Mem x L2 -> False) ->
  No_duplicates (L1 ++ L2).
Proof using.
  Hint Constructors Mem.
  induction L1; introv N1 N2 EQ; rew_list.
  auto.
  inverts N1 as N N1'. constructors.
    rewrite Mem_app_or_eq. rew_logic*.
    applys~ IHL1. introv Mx1 Mx2. applys* EQ x.
Qed.

Lemma No_duplicates_Filter : forall A (L:list A) P,
  No_duplicates L -> No_duplicates (Filter P L).
Proof using.
  Hint Constructors No_duplicates.
  introv H. induction H.
  rewrite* Filter_nil.
  rewrite Filter_cons. case_if.
    constructors*. introv N. false* Filter_Mem_inv N.
    auto.
Qed.

Lemma No_duplicates_length_le : forall A (L L':list A),
  No_duplicates L ->
  (forall x, Mem x L -> Mem x L') ->
  (length L <= length L')%nat.
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

Lemma No_duplicates_length_eq : forall A (L L':list A),
  No_duplicates L ->
  No_duplicates L' ->
  (forall x, Mem x L <-> Mem x L') ->
  (length L = length L')%nat.
Proof using.
  introv HL HL' EQ.
  forwards~: No_duplicates_length_le L L'. intros. rewrite~ <- EQ.
  forwards~: No_duplicates_length_le L' L. intros. rewrite~ EQ.
  math.
Qed.

Lemma No_duplicates_Nth : forall A (L : list A) n1 n2 a,
  No_duplicates L ->
  Nth n1 L a ->
  Nth n2 L a ->
  n1 = n2.
Proof using.
  introv NL. gen n1 n2. induction NL; introv N1 N2.
   inverts N1.
   inverts N1 as N1; inverts N2 as N2; autos~.
    apply Nth_mem in N2. rewrite <- Mem_mem in N2. false*.
    apply Nth_mem in N1. rewrite <- Mem_mem in N1. false*.
Qed.

Lemma Nth_No_duplicates : forall A (L : list A),
  (forall n1 n2 a,
    Nth n1 L a ->
    Nth n2 L a ->
    n1 = n2) ->
  No_duplicates L.
Proof using.
  introv NL. induction L; constructors.
   introv I. rewrite Mem_mem in I. lets (n&N): mem_Nth (rm I).
    forwards* Ab: NL Nth_here Nth_next. inverts Ab.
   apply IHL. introv N1 N2. forwards G: NL.
    applys Nth_next N1.
    applys Nth_next N2.
    inverts~ G.
Qed.

Lemma No_duplicates_inv_app : forall A (L1 L2 : list A),
  No_duplicates (L1 ++ L2) ->
  No_duplicates L1 /\ No_duplicates L2 /\ ~ exists x, mem x L1 /\ mem x L2.
Proof using.
  introv ND. splits.
   induction L1.
    constructors.
    rew_list in ND. inverts ND as ND1 ND2. rewrite Mem_app_or_eq in ND1. rew_logic* in ND1.
   induction L1.
    rew_list~ in ND.
    rew_list in ND. inverts~ ND.
   introv (x&I1&I2). rewrite <- Mem_mem in *. induction I1; rew_list in ND.
    inverts ND as ND1 ND2. false ND1. apply* Mem_app_or.
    apply IHI1. inverts~ ND.
Qed.


(* ---------------------------------------------------------------------- *)
(** * Fold on No_duplicates *)

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
(* ** Reasoning about equality under a [fold]. *)

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

(* ---------------------------------------------------------------------- *)
(* ** Remove_duplicates *)

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
(* ** Update of a functional list *)

Section UpdateProp.
Variables A : Type.
Implicit Types x : A.
Implicit Types l : list A.
Implicit Types n : nat.
Hint Constructors Nth.

Lemma Update_here : forall x y l,
  Update 0 x (y::l) (x::l).
Proof using.
  intros. splits.
  rew_length~.
  introv M H. inverts* M.
  autos*.
Qed.

Lemma Update_cons : forall i x y l l',
  Update i x l l' -> Update (S i) x (y::l) (y::l').
Proof using.
  introv (L&O&E). splits.
  rew_length~.
  introv M H. inverts* M.
  autos*.
Qed.

Lemma Update_app_l : forall i x l1 l1' l2,
  Update i x l1 l1' -> Update i x (l1++l2) (l1'++l2).
Proof using.
  introv (L&O&E). splits.
  rew_length~.
  introv M H. destruct (Nth_app_inv _ _ M).
    apply~ Nth_app_l.
    unpack. apply* Nth_app_r. math.
  apply~ Nth_app_l.
Qed.

Lemma Update_app_r : forall i j x l1 l2 l2',
  Update j x l2 l2' -> i = (j + length l1)%nat -> Update i x (l1++l2) (l1++l2').
Proof using.
  introv (L&O&E) Eq. splits.
  rew_length~.
  introv M H. destruct (Nth_app_inv _ _ M).
    apply~ Nth_app_l.
    unpack. apply* Nth_app_r. apply* O. math. math.
  apply* Nth_app_r.
Qed.

Lemma Update_length : forall i x l l',
  Update i x l l' -> length l = length l'.
Proof using. introv (L&O&E). auto. Qed.

Lemma Update_not_nil : forall i x l1 l2,
  Update i x l1 l2 -> l2 <> nil.
Proof using. introv (L&O&E) K. subst. inverts E. Qed.

End UpdateProp.


(* ---------------------------------------------------------------------- *)
(* ** Equality modulo equivalence relation *)

(** [list_equiv E l1 l2] asserts that the lists [l1] and [l2]
    are equal when their elements are compared modulo E *)

Definition list_equiv (A:Type) (E:binary A) : binary (list A) :=
   Forall2 E.

Section ListEquiv.
Hint Constructors Forall2.

Lemma list_equiv_equiv : forall A (E:binary A),
  equiv E -> equiv (list_equiv E).
Proof using.
  introv Equiv. unfold list_equiv. constructor.
  unfolds. induction x. auto. constructor; dauto.
  unfolds. induction x; destruct y; introv H; inversions H; dauto.
  unfolds. induction y; destruct x; destruct z; introv H1 H2;
   inversions H1; inversions H2; dauto.
Qed.

End ListEquiv.

(* -------------------------------------------------------------------------- *)

(* The [prefix] ordering on lists. *)

Section Prefix.

Variable A : Type.

(* A definition in terms of concatenation. See also [LibListZ]. *)

Definition prefix (ys xs : list A) :=
  exists zs, ys ++ zs = xs.

  (* TODO one could give an alternate definition of [prefix] as an
     inductive predicate with two cases: [Nil/Cons] and [Cons/Cons].
     This would give rise to a potentially useful induction principle.
     Or just prove this induction principle directly. *)

(* Ordering. *)

Lemma prefix_reflexive:
  forall xs,
  prefix xs xs.
Proof using.
  intros. exists (@nil A). eapply app_nil_r.
Qed.

Lemma prefix_antisymmetric:
  forall xs ys,
  prefix xs ys ->
  prefix ys xs ->
  xs = ys.
Proof using.
  introv (ws&?) (zs&?). subst ys. rew_list in *.
  forwards: app_eq_self_inv_l. { eauto. }
  forwards: app_eq_nil_inv. { eauto. }
  unpack. subst ws zs. rew_list. eauto.
Qed.

Lemma prefix_transitive:
  forall xs ys zs,
  prefix xs ys ->
  prefix ys zs ->
  prefix xs zs.
Proof using.
  introv [ xs' ? ] [ ys' ? ].
  subst. rew_list. unfold prefix. eauto.
Qed.

(* [prefix] and [nil]. *)

Lemma prefix_nil:
  forall xs,
  prefix nil xs.
Proof using.
  intros. exists xs. eapply app_nil_l.
Qed.

Lemma prefix_nil_inverse:
  forall xs,
  prefix xs nil ->
  xs = nil.
Proof using.
  introv (ys&?).
  forwards: app_eq_nil_inv. eauto.
  unpack. eauto.
Qed.

(* [prefix] and [cons]. *)

Lemma prefix_cons_inverse: (* TEMPORARY rename: [prefix_cons_r_inverse] *)
  forall xs y ys,
  prefix xs (y :: ys) ->
  xs = nil \/ exists xs', xs = y :: xs' /\ prefix xs' ys.
Proof using.
  introv (zs&Heq).
  destruct xs; [ eauto | right ].
  rew_list in Heq. injects Heq.
  unfold prefix. eauto.
Qed.

Lemma use_prefix_cons: (* TEMPORARY rename: [prefix_cons_l_inverse] *)
  forall x xs ys,
  prefix (x :: xs) ys ->
  exists ys', ys = x :: ys'.
Proof using.
  introv [ slack ? ]. rew_list in *. exists (xs ++ slack). eauto.
Qed.

Lemma prefix_cons_cons:
  forall x xs1 xs2,
  prefix xs1 xs2 ->
  prefix (x :: xs1) (x :: xs2).
Proof using.
  introv (ys&?). subst. exists ys. rew_list. eauto.
Qed.

Lemma prefix_cons_cons_inverse:
  forall x1 x2 xs1 xs2,
  prefix (x1 :: xs1) (x2 :: xs2) ->
  x1 = x2 /\ prefix xs1 xs2.
Proof using.
  intros.
  forwards: prefix_cons_inverse; eauto.
  branches; unpack; try split; congruence.
Qed.

Lemma prefix_cons_cons_eq:
  forall x xs1 xs2,
  prefix (x :: xs1) (x :: xs2) = prefix xs1 xs2.
Proof using.
  intros. extens. split.
  { eapply prefix_cons_cons_inverse. }
  { eapply prefix_cons_cons. }
Qed.

(* [prefix] and [++]. *)

Lemma prefix_concat:
  forall xs ys zs,
  prefix xs ys ->
  prefix xs (ys ++ zs).
Proof using.
  unfold prefix. introv (ws&?). subst ys.
  exists (ws ++ zs). rew_list. eauto.
Qed.

Lemma prefix_concat_simplify:
  forall xs ys1 ys2,
  prefix ys1 ys2 ->
  prefix (xs ++ ys1) (xs ++ ys2).
Proof using.
  introv (ws&?). subst ys2. exists ws. rew_list. eauto.
Qed.

Lemma eliminate_common_prefix:
  forall xs ys zs,
  prefix (xs ++ ys) (xs ++ zs) ->
  prefix ys zs.
Proof using.
  introv [ slack ? ]. exists slack.
  rew_list in *.
  eauto using app_cancel_l.
Qed.

Lemma prefix_app_r_inverse:
  forall ys1 xs ys2,
  prefix xs (ys1 ++ ys2) ->
  prefix xs ys1 \/
  exists ys2a, xs = ys1 ++ ys2a /\ prefix ys2a ys2.
Proof using.
  induction ys1 as [ | y ys1 ]; simpl; intros.
  { right. exists xs. rew_list in *. eauto. }
  { destruct xs as [ | x xs ].
    { eauto using prefix_nil. }
    { rew_list in *.
      forwards: prefix_cons_cons_inverse. { eauto. } unpack. subst y.
      forwards [ ? | (ys2a&?&?) ]: IHys1. { eauto. }
      { eauto using prefix_cons_cons. }
      { right. eexists ys2a. rew_list. subst xs. eauto. }
    }
  }
Qed.

(* [prefix] and [snoc]. *)

Lemma prove_prefix_snoc:
  forall x xs ys zs,
  xs ++ x :: ys = zs ->
  prefix (xs & x) zs.
Proof using.
  intros. exists ys. rew_list. eauto.
Qed.

Lemma use_prefix_snoc:
  forall x xs ys zs,
  prefix (xs & x) ys ->
  ys = xs ++ zs ->
  exists zs', zs = x :: zs'.
Proof.
  introv h ?. subst.
  forwards: eliminate_common_prefix h.
  eauto using use_prefix_cons.
Qed.

Lemma prefix_last: (* TEMPORARY should be: use_prefix_snoc *)
  forall x xs ys,
  prefix (xs & x) ys ->
  prefix xs ys.
Proof using.
  introv [ zs ? ]. exists (x :: zs). rew_list in *. eauto.
Qed.

(* [prefix] and [length]. See also [LibListZ]. *)

Lemma prefix_length:
  forall ys xs,
  prefix ys xs ->
  length ys <= length xs.
Proof using.
  intros ys xs [ zs ? ]. subst xs. rew_list. math.
Qed.

Lemma prefix_snoc_length:
  forall ys y xs,
  prefix (ys & y) xs ->
  length ys < length xs.
Proof using.
  intros ys y xs [ zs ? ]. subst xs. rew_list. math.
Qed.

(* [prefix] and [No_duplicates]. *)

Lemma no_duplicates_prefix:
  forall xs ys,
  No_duplicates ys ->
  prefix xs ys ->
  No_duplicates xs.
Proof using.
  introv ? (zs&?). subst.
  forwards: No_duplicates_inv_app; eauto.
  tauto.
Qed.

End Prefix.

Hint Resolve
  prefix_reflexive
  prefix_nil
  prefix_cons_cons
  prefix_concat
  prefix_concat_simplify
  prove_prefix_snoc
: prefix.

(* -------------------------------------------------------------------------- *)

Section PrefixClosed.

Variable A : Type.

Implicit Types xs ys : list A.

(* Prefix-closedness. *)

Definition prefix_closed (P : list A -> Prop) :=
  forall xs ys,
  P ys ->
  prefix xs ys ->
  P xs.

Lemma prefix_closed_nil:
  forall (P : list A -> Prop) xs,
  prefix_closed P ->
  P xs ->
  P nil.
Proof using.
  eauto with prefix.
Qed.

(* Prefix closure. *)

Definition prefix_closure (P : list A -> Prop) : list A -> Prop :=
  fun xs => exists ys, prefix xs ys /\ P ys.

Definition prefix_closure_alt (P : list A -> Prop) : list A -> Prop :=
  fun xs => exists ys, P (xs ++ ys).

Lemma prefix_closure_eq:
  forall P,
  prefix_closure P = prefix_closure_alt P.
Proof using.
  intros. extens; intros xs; split; unfold prefix_closure, prefix_closure_alt, prefix.
  { introv (ys&(zs&?)&?). subst. eauto. }
  { introv (ys&?). eauto. }
Qed.

Lemma prefix_closure_is_prefix_closed:
  forall P,
  prefix_closed (prefix_closure P).
Proof.
  unfold prefix_closed, prefix_closure.
  introv (zs&?&?). eauto using prefix_transitive.
Qed.

(* The relation [fun xs => prefix xs ys] is the prefix closure of the
   singleton [ys]. Thus, it is prefix-closed. *)

Lemma prefix_closure_singleton:
  forall ys : list A,
  (fun xs => prefix xs ys) = prefix_closure (= ys).
Proof using.
  intros. extens; intros xs. unfold prefix_closure.
  split. eauto. intros (?&?&?). subst. eauto.
Qed.

Lemma prefix_closed_prefix:
  forall ys : list A,
  prefix_closed (fun xs => prefix xs ys).
Proof using.
  intros. rewrite prefix_closure_singleton.
  eapply prefix_closure_is_prefix_closed.
Qed.

End PrefixClosed.

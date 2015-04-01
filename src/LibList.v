(**************************************************************************
* TLC: A library for Coq                                                  *
* Lists                                                                   *
**************************************************************************)

Set Implicit Arguments. 
Generalizable Variables A B.
Require Import LibTactics LibLogic LibReflect LibOperation
 LibProd LibOption LibNat LibInt LibWf LibRelation.
Require Export List.
Open Local Scope nat_scope.
Open Local Scope comp_scope.


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
Variables (A B C : Type) (IA : Inhab A). 
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

Fixpoint mem x l := 
  match l with
  | nil => false
  | y::l' => (x '= y) || mem x l'
  end.

Fixpoint remove x l := (* DEPRECATED *)
  match l with
  | nil => nil
  | y::l' => let acc := remove x l' in
             If x = y then acc else y::acc
  end.

Fixpoint removes l2 l1 := (* DEPRECATED *)
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

Implicit Arguments fold_left [[A] [B]].
Implicit Arguments fold_right [[A] [B]].
Implicit Arguments append [[A]].
Implicit Arguments concat [[A]].
Implicit Arguments rev [[A]].
Implicit Arguments length [[A]].
Implicit Arguments mem [[A]].
Implicit Arguments remove [[A]].
Implicit Arguments removes [[A]].
Implicit Arguments take_drop_last [[A] [IA]].
Implicit Arguments nth_def [[A]].
Implicit Arguments nth [[A] [IA]].
Implicit Arguments update [[A]].
Implicit Arguments make [[A]].

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
Variable A B : Type.
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
Variable A B : Type.
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

(* ---------------------------------------------------------------------- *)
(** ** Map *)

Section MapProp.
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
End MapProp.

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

End FilterProp.


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
End MemProp.


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

Implicit Arguments length_zero_inv [A l].
Implicit Arguments take_struct [A].

Module TakeInt.
Require Import LibInt.
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


(* ********************************************************************** *)
(** * Association lists *)

(* ---------------------------------------------------------------------- *)
(** ** Operations *)

Section Assoc.
Context {A B : Type}.
Variables (IB:Inhab B).
Implicit Types x : A.
Implicit Types l : list (A*B).

Fixpoint assoc k l : B :=
  match l with 
  | nil => arbitrary
  | (x,v)::l' => If x = k then v else assoc k l' 
  end.

Definition mem_assoc k := 
  exists_st (fun p:A*B => k '= fst p).

Definition keys :=
  @map (A*B) A (@fst _ _).

Fixpoint remove_assoc k l : list (A*B) :=
  match l with 
  | nil => nil
  | (x,v)::l' => 
      If k = x 
        then l' 
        else (x,v)::(remove_assoc k l')
  end.

End Assoc.

Implicit Arguments assoc [[A] [B] [IB]].
Implicit Arguments mem_assoc [[A] [B]].
Implicit Arguments keys [[A] [B]].
Implicit Arguments remove_assoc [[A] [B]].


(* ---------------------------------------------------------------------- *)
(** ** Properties *)

Section AssocProperties.
Variable (A B : Type) (IB:Inhab B).
Implicit Types x : A.
Implicit Types l : list (A*B).

Lemma assoc_cons : forall k x y l,
  assoc k ((x,y)::l) = If x = k then y else assoc k l.
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
    If x = x' then l else (x',y)::remove_assoc x l.
Proof using. auto. Qed.

End AssocProperties.





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
  autorewrite with rew_app in *.
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
  autorewrite with rew_list in *.
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

Lemma app_not_empty_l : forall l1 l2,
  l1 <> nil -> l1 ++ l2 <> nil.
Proof using. introv NE K. apply NE. destruct~ (app_eq_nil_inv _ _ K). Qed.

Lemma app_not_empty_r : forall l1 l2,
  l2 <> nil -> l1 ++ l2 <> nil.
Proof using. introv NE K. apply NE. destruct~ (app_eq_nil_inv _ _ K). Qed.

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

(* TODO: Forall2_weaken *)

End PropProperties2.

Implicit Arguments Forall2_last_inv [A1 A2 P l1 r' x1].

(* todo : inversion lemmas for other predicates *)


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

(* TODO: Exists_weaken *)

End ExistsProp.


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
    left~. intuit. rew_length.
    right*. exists x0. split~. math.
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

End NthProperties.

(* ---------------------------------------------------------------------- *)
(* ** Mem *)

Section MemFacts.
Hint Constructors Mem.

Lemma Mem_induct : forall (A : Type) (x : A) (P : list A -> Prop),
  (forall l : list A, P (x :: l)) ->
  (forall (y : A) (l : list A), Mem x l -> x <> y -> P l -> P (y :: l)) ->
  (forall l : list A, Mem x l -> P l).
Proof.
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

Lemma Mem_inv : forall A (L:list A) x y,
  Mem x (y::L) -> x = y \/ x <> y /\ Mem x L.
Proof using. introv H. tests: (x = y). eauto. inverts H. false. eauto. Qed.

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
Proof.
  intros. induction L.
  rewrite Filter_nil. introv M. inverts M.
  rewrite Filter_cons. case_if.
    introv M. inverts M; false.
    auto.
Qed.

Lemma Filter_Mem : forall x (L:list A) (P:A->Prop),
  Mem x L -> P x -> Mem x (Filter P L).
Proof.
  Hint Constructors Mem.
  introv H Px. induction H using Mem_induct.
  rewrite Filter_cons. case_if*.
  rewrite Filter_cons. case_if*.
Qed.

Lemma Filter_Mem_inv : forall x (L:list A) P,
  Mem x (Filter P L) -> Mem x L /\ P x.
Proof.
  Hint Constructors Mem.
  introv M. induction L.
  rewrite Filter_nil in M. inverts M.
  rewrite Filter_cons in M. case_if. inverts* M. autos*.
Qed.

Lemma Filter_length_le : forall (L:list A) P,
  (length (Filter P L) <= length L)%nat.
Proof.
  intros. induction L. 
  rewrite Filter_nil. math.
  rewrite Filter_cons. case_if; rew_length; math.
Qed.

Lemma Filter_neq_Mem_length : forall x (L:list A),
  Mem x L -> (length (Filter (<> x) L) < length L)%nat.
Proof.
  introv M. induction L.
  inverts M.
  rewrite Filter_cons. case_if.
    inverts M. false. rew_length. forwards~: IHL. math.   
    lets: (Filter_length_le L (<> x)). rew_length. math.
Qed.

Lemma Filter_No_duplicates : forall (L:list A) P, 
  No_duplicates L -> No_duplicates (Filter P L).
Proof.
  Hint Constructors No_duplicates.
  introv H. induction H.
  rewrite* Filter_nil. 
  rewrite Filter_cons. case_if.
    constructors*. introv N. false* Filter_Mem_inv N.
    auto.
Qed.

End FilterFacts.

(* ---------------------------------------------------------------------- *)
(* ** Remove_duplicates and No_duplicates *)

Lemma Remove_duplicates_spec : forall A (L L':list A),
  L' = Remove_duplicates L ->
  No_duplicates L' /\ (forall x, Mem x L' <-> Mem x L).
Proof using.
  Hint Constructors Mem No_duplicates.
  introv. gen L'. induction L; introv E; simpls.
  subst. splits*.
  sets_eq L'': (Remove_duplicates L). forwards~ [E' M]: IHL. splits~.
    subst L'. constructors. applys Filter_neq. applys* Filter_No_duplicates.
    subst L'. intros x. lets (M1&M2): M x. iff N.
      inverts N as R. auto. lets: Filter_Mem_inv R. constructors*.
      lets [E|(H1&H2)]: Mem_inv N. subst*. constructors. applys* Filter_Mem.
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
    intuit. apply* Nth_app_r. math.
  apply~ Nth_app_l.
Qed.

Lemma Update_app_r : forall i j x l1 l2 l2',
  Update j x l2 l2' -> i = (j + length l1)%nat -> Update i x (l1++l2) (l1++l2').
Proof using.
  introv (L&O&E) Eq. splits.
  rew_length~.
  introv M H. destruct (Nth_app_inv _ _ M).
    apply~ Nth_app_l.
    intuit. apply* Nth_app_r. apply* O. math. math.
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

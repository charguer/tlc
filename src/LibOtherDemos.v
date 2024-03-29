(**************************************************************************
* TLC: A library for Coq                                                  *
* Examples for other tactics provided by TLC                              *
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics.
From TLC Require Import LibLogic LibEqual LibList LibRelation LibWf LibList LibLN.


(* ---------------------------------------------------------------------- *)
(** ** Demo of extens tactics *)

Lemma test_extensionality_1 : forall A1 (P Q :  A1->Prop),
  (forall x1, P x1 <-> Q x1) ->
  P = Q.
Proof using.
  intros. applys extensionality. hnf.
Abort.

Lemma test_extensionality_2 : forall A1 (A2: A1->Type) (P Q : forall (x1:A1) (x2:A2 x1), Prop),
  (forall x1 x2, P x1 x2 <-> Q x1 x2) ->
  P = Q.
  intros. applys extensionality. hnf.
Abort.

Section FuncExtDepTest.
Variables (A1 : Type).
Variables (A2 : forall (x1 : A1), Type).
Variables (A3 : forall (x1 : A1) (x2 : A2 x1), Type).
Variables (A4 : forall (x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type).

Lemma test_fun_ext_3 : forall (f g : forall (x1:A1) (x2:A2 x1) (x3:A3 x2), A4 x3),
  (forall x1 x2 x3, f x1 x2 x3 = g x1 x2 x3) ->
  f = g.
Proof using. intros. applys extensionality. hnf. Abort.

End FuncExtDepTest.

Lemma prop_ext_1_test : forall (P Q : Prop),
  (P <-> Q) ->
  P = Q.
Proof using.
  intros. applys extensionality. simpl extensionality_hyp.
Abort.


(* ---------------------------------------------------------------------- *)
(** ** Demo of LibLogic tactics *)
Lemma absurds_demo : forall (P Q : Prop),
  P /\ (~ P) /\ (Q \/ ~ P).
Proof using.
  intros. splits.
  { absurds ;=> H. admit. }
  { absurds ;=> H. admit. }
  { absurds ;=> (H1&H2). admit. }
Abort.


(* ********************************************************************** *)
(** * How to do recursion/induction on terms with list of subterms *)

Module SubtermIndDemos.

Import LibLogic LibList.

(** Definition of trees with list of subtrees *)

Inductive tree : Type :=
  | leaf : nat -> tree
  | node : list tree -> tree.

(** Example of a primitive-recursive function on trees
    using an inlined fixed point -- not recommended *)

Fixpoint tree_incr' (t:tree) :=
  match t with
  | leaf n => leaf (S n)
  | node ts =>
     node ((fix aux ts := match ts with
            | nil => nil
            | t::ts' => tree_incr' t :: aux ts'
            end) ts)
  end.

(** Same example but using the map function on lists
    -- recommended
    -- this works only because List.map has exactly
    the same form as the local [fix] used above.
    -- if you wanted to use LibList.map instead of
    List.map, it would not work; you would have to
    either use the optimal fixed point (see LibFixDemos)
    or you would have to exploit [List.map = LibList.map] *)

Fixpoint tree_incr (t:tree) :=
  match t with
  | leaf n => leaf (S n)
  | node ts => node (List.map tree_incr ts)
  end.

(** Another example -- recommended *)

Fixpoint tree_map (f:nat->nat) (t:tree) :=
  match t with
  | leaf n => leaf (f n)
  | node ts => node (List.map (tree_map f) ts)
  end.

(** Another example using List.fold -- recommended *)

Fixpoint tree_sum (t:tree) :=
  match t with
  | leaf n => n
  | node ts => List.fold_left (fun acc t => acc + tree_sum t) ts 0
  end.

(** Proof of the recursion principle *)

Section Tree_induct.
(* Note: some hypotheses are given directly by [Check tree_ind] *)
Variables
(P : tree -> Prop)
(Q : list tree -> Prop)
(P1 : forall n, P (leaf n))
(P2 : forall ts, Q ts -> P (node ts))
(Q1 : Q nil)
(Q2 : forall t ts, P t -> Q ts -> Q (t::ts)).

Fixpoint tree_induct_gen (t : tree) : P t :=
  match t as x return P x with
  | leaf n => P1 n
  | node ts => P2
      ((fix tree_list_induct (ts:list tree) : Q ts :=
      match ts as x return Q x with
      | nil   => Q1
      | t::ts' => Q2 (tree_induct_gen t) (tree_list_induct ts')
      end) ts)
  end.

End Tree_induct.

(** Example of a direct inductive proof -- not recommended *)

Lemma tree_map_pred_succ_1 : forall t,
  tree_map pred (tree_map S t) = t.
Proof using.
  intros. pattern t. match goal with |- ?F _ => sets P: F end.
  eapply tree_induct_gen with (Q := Forall P); subst P; simpl; intros.
  fequals.
  fequals. induction ts; simpl.
    fequals.
    inverts H. fequals~.
  constructors.
  constructors~.
Qed.

(** Proof of the induction principle with Forall *)

Lemma tree_induct_forall : forall (P : tree -> Prop),
  (forall n : nat, P (leaf n)) ->
  (forall ts : list tree, Forall P ts -> P (node ts)) ->
  forall t : tree, P t.
Proof using.
  introv Hl Hn. eapply tree_induct_gen with (Q := Forall P); intros.
  auto. auto. constructors~. constructors~.
Qed.

(** Example of an inductive proof with Forall
    -- recommended *)

Lemma tree_map_pred_succ_2 : forall t,
  tree_map pred (tree_map S t) = t.
Proof using.
  intros. induction t using tree_induct_forall; simpl.
  fequals.
  fequals. induction ts; simpl.
    auto.
    inverts H. fequals~.
Qed.

(** Proof of the induction principle with Mem *)

Lemma tree_induct_mem : forall (P : tree -> Prop),
  (forall n : nat, P (leaf n)) ->
  (forall ts : list tree,
    (forall t, mem t ts -> P t) -> P (node ts)) ->
  forall t : tree, P t.
Proof using.
  introv Hl Hn. eapply tree_induct_gen with (Q := fun ts =>
    forall t, mem t ts -> P t); intros.
  auto. auto. inverts H. inverts~ H1.
Qed.

#[global]
Hint Constructors mem.

(** Example of an inductive proof with Mem
    -- usually not as good as the one with [Forall] *)

Lemma tree_map_pred_succ_3 : forall t,
  tree_map pred (tree_map S t) = t.
Proof using.
  intros. induction t using tree_induct_mem; simpl.
  fequals.
  fequals. induction ts; simpl.
    fequals.
    fequals.
      apply H. constructor.
      apply IHts. introv M. apply H. auto.
Qed.

(** Definition of the relation "immediate subtree of" *)

Import LibRelation LibWf.

Inductive subtree : binary tree :=
  | subtree_intro : forall t ts,
     mem t ts -> subtree t (node ts).
  (* there is typically more than one case here *)

#[global]
Hint Constructors subtree.

(** Proof of well-foundedness of the subtree relation *)

Lemma subtree_wf : wf subtree.
Proof using.
  intros t. induction t using tree_induct_mem;
  constructor; introv K; inversions~ K.
Qed.

(** Example of a proof on the well-founded subtree order
    -- usually a bit longer, so not recommended *)

Lemma tree_map_pred_succ_4 : forall t,
  tree_map pred (tree_map S t) = t.
Proof using.
  intros. induction_wf IH: subtree_wf t.
  destruct t as [|ts]; simpl.
  fequals.
  fequals. induction ts; simpl.
    fequals.
    fequals.
      applys IH. auto.
      applys IHts. introv M. inverts M.
       auto. (* apply IH. constructors. constructors. *)
Qed.

End SubtermIndDemos.


(* ********************************************************************** *)
(** * Tactics exported by LibVar *)

Module LibVarDemos.
Import LibList LibLN.
Section LibVarDemo.
Implicit Types x y : var.

(* ---------------------------------------------------------------------- *)
(** ** Demo for notin *)

Lemma test_notin_solve_1 : forall x E F G,
  x \notin E \u F -> x \notin G -> x \notin (E \u G).
Proof using.
  intros. dup.
  notin_simpl. notin_solve. notin_solve.
  notin_solve.
Qed.

Lemma test_notin_solve_2 : forall x y E F G,
  x \notin E \u \{y} \u F -> x \notin G ->
  x \notin \{y} /\ y \notin \{x}.
Proof using.
  split. notin_solve. notin_solve.
Qed.

Lemma test_notin_solve_3 : forall x y,
  x <> y -> x \notin \{y} /\ y \notin \{x}.
Proof using.
  split. notin_solve. notin_solve.
Qed.

Lemma test_notin_solve_4 : forall x y,
  x \notin \{y} -> x <> y /\ y <> x.
Proof using.
  split. notin_solve. notin_solve.
Qed.

Lemma test_notin_false_1 : forall x y E F G,
  x \notin (E \u \{x} \u F) -> y \notin G.
Proof using.
  intros. dup 3.
    false. notin_false.
    notin_false.
    notin_false.
Qed.

Lemma test_notin_false_2 : forall x y : var,
  x <> x -> y = x.
Proof using.
  intros. notin_false.
Qed.

Lemma test_neq_solve : forall x y E F,
  x \notin (E \u \{y} \u F) -> y \notin E ->
  y <> x /\ x <> y.
Proof using.
  split. notin_solve. notin_solve.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Demo for fresh *)

Lemma test_fresh_solve_1 : forall xs L1 L2 n,
  fresh (L1 \u L2) n xs -> fresh L1 n xs.
Proof using.
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_2 : forall xs L1 L2 n,
 fresh (L1 \u L2) n xs -> fresh L2 n xs.
Proof using.
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_3 : forall xs L1 L2 n,
 fresh (L1 \u L2) n xs -> fresh \{} n xs.
Proof using.
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_4 : forall xs L1 L2 n,
 fresh (L1 \u L2) n xs -> fresh L1 (length xs) xs.
Proof using.
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_5 : forall xs L1 n m,
  m = n ->
  fresh L1 m xs ->
  fresh L1 n xs.
Proof using.
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_6 : forall xs L1 L2 n m,
  m = n ->
  fresh (L1 \u L2) n xs ->
  fresh L1 m xs.
Proof using.
  intros. fresh_solve.
Qed.

Lemma test_fresh_solve_7 : forall xs L1 L2 n m,
  n = m ->
  fresh (L1 \u L2) n xs ->
  fresh L1 m xs.
Proof using.
  intros. fresh_solve.
Qed.

(* ---------------------------------------------------------------------- *)
(** ** Demo of automation of [notin] *)

(* LibVar exports the following hints:
     Hint Extern 1 (_ \notin _) => notin_solve.
     Hint Extern 1 (_ <> _ :> var) => notin_solve.
     Hint Extern 1 ((_ \notin _) /\ _) => splits. *)

Lemma test_notin_by_auto : forall x E F G,
  x \notin E \u F -> x \notin G -> x \notin (E \u G).
Proof using. auto. Qed.

Lemma test_neq_by_auto : forall x y E,
  x \notin E \u \{y} -> y <> x.
Proof using. auto. Qed.

Lemma test_notin_false_by_hand : forall x,
  ~ x \notin \{x}.
Proof using. intros_all. notin_false. Qed.

Hint Extern 1 (~ _ \notin _) => intros_all; notin_false.

Lemma test_notin_false_by_auto : forall x,
  ~ x \notin \{x}.
Proof using. intros_all. notin_false. Qed.

(* Comment: using the following hint is a bad idea because it will
            lead to very inefficient proof scripts.
   Hint Extern 1 (False) => notin_false. *)


(* ---------------------------------------------------------------------- *)
(** ** Demo of pick_fresh_gen *)

Parameter trm : Type.
Parameter fv : trm -> vars.

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : trm => fv x) in
  constr:(A \u B \u C).

Ltac pick_fresh Y :=
  let L := gather_vars in (pick_fresh_gen L Y).

Lemma test_pick_fresh :
  forall (x y z : var) (L1 L2 L3 : vars) (t1 t2 : trm), True.
Proof using.
  intros. pick_fresh a.
Abort.

End LibVarDemo.
End LibVarDemos.





(* ---------------------------------------------------------------------- *)
(** ** Demo of LibSet tactics *)

From TLC Require Import LibSet.

Lemma inter_union_disjoint_right:
  forall A (E F G : set A),
  F \# G ->
  (E \u F) \n G = (E \n G).
Proof using.
  set_prove.
  (* intros. set_norm. set_specialize. set_norm. tauto. *)
Qed. (* demo *)

Lemma inter_union_subset_right:
  forall A (E F G : set A),
  F \c G ->
  (E \u F) \n G = (E \n G) \u F.
Proof using.
  set_prove.
Qed. (* demo *)

Lemma inter_covariant:
  forall A (E E' F F' : set A),
  E \c E' ->
  F \c F' ->
  (E \n F) \c (E' \n F').
Proof using.
  set_prove.
Qed. (* demo *)

Lemma set_decompose_inter_right :
  forall A (E F : set A),
  E = (E \n F) \u (E \- F).
Proof using.
  set_prove_classic.
Qed. (* demo *)

Lemma set_decompose_union_right :
  forall A (E F : set A),
  (E \u F) = E \u (F \- E).
Proof using.
  set_prove_classic.
Qed. (* demo *)

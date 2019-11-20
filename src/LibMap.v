(**************************************************************************
* TLC: A library for Coq                                                  *
* Finite maps                                                             *
**************************************************************************)

Set Implicit Arguments.
Generalizable Variables A B.
From TLC Require Import LibTactics LibLogic LibReflect LibOption
  LibRelation LibLogic LibOperation LibEpsilon LibMonoid LibSet.
From TLC Require Export LibContainer.

Local Open Scope set_scope.


(* ********************************************************************** *)
(** * Construction of maps as functions *)

(* ---------------------------------------------------------------------- *)
(** ** Basic definitions *)

Definition map (A B : Type) := A -> option B.

Section Operations.
Variables (A B : Type).
Implicit Types k : A.
Implicit Types x : B.
Implicit Types M N : map A B.
Implicit Types E : set A.

Definition empty_impl : map A B :=
  fun _ => None.

Definition single_bind_impl k x :=
  fun k' => If k = k' then Some x else None.

Definition binds_impl M k x :=
  M k = Some x.

Definition union_impl M N :=
  fun k => match N k with
           | None => M k
           | Some v => Some v
           end.

Definition remove_impl M E :=
  fun k => If k \in E then None else M k.

Definition restrict_impl M E :=
  fun k => If k \in E then M k else None.

Definition dom_impl M :=
  set_st (fun k => M k <> None).

Definition disjoint_impl M N :=
  disjoint (dom_impl M) (dom_impl N).

Definition index_impl M k :=
  k \in (dom_impl M : set A).

(* -- TODO: incl_impl *)

End Operations.

Definition read_impl A `{Inhab B} (M:map A B) (k:A) :=
  match M k with
  | None => arbitrary
  | Some v => v
  end.

Definition fold_impl A B C (m:monoid_op C) (f:A->B->C) (M:map A B) :=
  LibContainer.fold m (fun p => let '(a,b) := p in f a b)
    (\set{ p | exists k x, p = (k, x) /\ binds_impl M k x }).


(* ---------------------------------------------------------------------- *)
(** ** Notation through typeclasses *)

Instance empty_inst : forall A B, BagEmpty (map A B).
  constructor. rapply (@empty_impl A B). Defined.

Instance single_bind_inst : forall A B, BagSingleBind A B (map A B).
  constructor. rapply (@single_bind_impl A B). Defined.

Instance binds_inst : forall A B, BagBinds A B (map A B).
  constructor. rapply (@binds_impl A B). Defined.

Instance union_inst : forall A B, BagUnion (map A B).
  constructor. rapply (@union_impl A B). Defined.

Instance remove_inst : forall A B, BagRemove (map A B) (set A).
  constructor. rapply (@remove_impl A B). Defined.

Instance restrict_inst : forall A B, BagRestrict (map A B) (set A).
  constructor. rapply (@restrict_impl A B). Defined.

Instance read_inst : forall A `{Inhab B}, BagRead A B (map A B).
  constructor. rapply (@read_impl A B H). Defined.

Instance dom_inst : forall A B, BagDom (map A B) (set A).
  constructor. rapply (@dom_impl A B). Defined.

Instance disjoint_inst : forall A B, BagDisjoint (map A B).
  constructor. rapply (@disjoint_impl A B). Defined.

Instance index_inst : forall A B, BagIndex A (map A B).
  constructor. rapply (@index_impl A B). Defined.

Instance fold_inst : forall A B C, BagFold C (A->B->C) (map A B).
  constructor. rapply (@fold_impl A B C). Defined.

Global Opaque map empty_inst single_bind_inst binds_inst
 union_inst restrict_inst remove_inst read_inst
 dom_inst disjoint_inst index_inst fold_inst.

Instance Inhab_map : forall A, Inhab (map A B).
Proof using. intros. apply (Inhab_of_val (@empty_impl A B)). Qed.


(* Note: we may check that [update] is derivable via [bag_update_as_union_single]
      Instance update_inst : forall A B, BagUpdate A B (map A B).
      Proof. typeclass. Qed. 
*)

(* ---------------------------------------------------------------------- *)
(** ** TEMPORARY *)

(*-- LATER: make [finite] a typeclass, define [finite_impl]  
     using [dom_impl], and prove a lemma [finite_eq] of type
     [finite M = finite (dom M)].
 *)

Definition finite A B (M:map A B) :=
  finite (dom M).


(* ********************************************************************** *)
(* Characterizations *)

Section Reformulation.
Transparent binds dom union.
Transparent map empty_inst single_bind_inst binds_inst
 union_inst restrict_inst remove_inst read_inst
 dom_inst disjoint_inst index_inst fold_inst.

Lemma binds_eq_indom_read : forall A `{Inhab B} (M:map A B) x v,
  binds M x v = (x \indom M /\ M[x] = v).
Proof using.
  intros. simpl. unfold dom_impl, read_impl, binds_impl.
  extens. rew_set. iff R (N&R).
    rewrite R. split~. congruence.
    destruct (M x). subst~. false.
Qed.

Lemma dom_eq_set_of_binds : forall A B (M:map A B),
  dom M = \set{ k | exists v, binds M k v }.
Proof using.
  intros. simpl. unfold dom_impl, binds_impl.
  applys set_st_eq. intros k. iff R.
    destruct (M k). eauto. false.
    destruct R. congruence.
Qed.

Lemma index_eq_indom : forall A B (M:map A B) k,
  index M k = (k \indom M).
Proof using. auto. Qed.

Lemma disjoint_eq_disjoint_dom : forall A B (M N:map A B),
  disjoint M N = disjoint (dom M) (dom N).
Proof using. auto. Qed.

Lemma fold_eq_fold_pairs : forall A B C (m:monoid_op C) (f:A->B->C) (M:map A B),
  fold m f M = LibContainer.fold m (fun p => let '(a,b) := p in f a b)
    (\set{ p | exists k x, p = (k, x) /\ binds_impl M k x }).
Proof using. auto. Qed.

Lemma update_eq_union_single : forall A B (M:map A B) k x,
  M[k:=x] = M \u (k \:= x).
Proof using. auto. Qed.

(* only for internal use *)
Lemma update_impl_eq : forall A B (M:map A B) k x,
  M[k:=x] = (fun k' => If k = k' then Some x else M k').
Proof using.
  intros. rewrite update_eq_union_single.
  simpl. unfold single_bind_impl, union_impl.
  apply fun_ext_1. intros k'. case_if~.
Qed.

End Reformulation.


(* ********************************************************************** *)
(** * Properties of maps *)
(*TODO: under construction *)

Section Properties.
Transparent map empty_inst single_bind_inst binds_inst
 union_inst restrict_inst remove_inst read_inst
 dom_inst disjoint_inst index_inst fold_inst.

Hint Extern 1 (Some _ <> None) => congruence.
Hint Extern 1 (None <> Some _) => congruence.

(* ---------------------------------------------------------------------- *)
(** extens *)

(* --LATER: state some extensionality *)

(* ---------------------------------------------------------------------- *)
(** index *)

Lemma index_of_indom : forall A B (M:map A B) k,
  k \indom M -> 
  index M k.
Proof using. intros. rewrite~ index_eq_indom. Qed.


(* ---------------------------------------------------------------------- *)
(** dom *)

Lemma dom_empty : forall A B,
  dom (\{} : map A B) = (\{} : set A).
Proof using.
  intros. simpl. unfold dom_impl. simpl. unfold binds_impl, empty_impl.
  apply set_ext. intros x. rewrite in_set_st_eq. iff R.
  false. false. (* apply @in_empty. *)
Qed.

Lemma dom_single : forall A B (k:A) (x:B),
  dom (k\:=x) = \{k}.
Proof using.
  intros. simpl. unfold binds_impl, single_bind_impl, dom_impl.
  apply set_ext. intros y. rewrite in_set_st_eq. iff R; case_if~.
  rewrite in_single_eq. auto.
Qed.

Lemma dom_union : forall A B (M N : map A B),
  dom (M \u N) = dom M \u dom N.
Proof using.
  intros. simpl. unfold dom_impl, union_impl.
  rew_set. intros x. rew_set. iff R; destruct* (N x).
Qed.


(* ---------------------------------------------------------------------- *)
(** indom *)

Lemma indom_empty_inv : forall A B (x:A),
  x \indom (\{} : map A B) ->
  False.
Proof using.
  introv M. rewrite dom_empty in *. applys @in_empty M; typeclass. 
Qed.

(* TODO CLEAN UP after migration *)
  (* old proof:
  intros. rewrite dom_empty in *. eapply in_empty; typeclasses eauto with typeclass_instances. *)
  (* new proof:
  introv M. rewrite dom_empty in *. eapply @in_empty. 2: eapply M. typeclasses eauto with typeclass_instances. *)


(* ---------------------------------------------------------------------- *)
(** prove empty *)

Lemma eq_empty_of_not_binds : forall (A B : Type) (M : map A B),
  (forall x k, ~ binds M x k) -> 
  M = \{}.
Proof using.
  intros A B M. simpl. unfold empty_impl, binds_impl.
  intros H. apply fun_ext_1. intros x. cases (M x); auto_false*.
Qed.

Lemma dom_empty_inv : forall A B (M : map A B),
  dom M = \{} -> 
  M = \{}.
Proof using.
  introv H. simpls. unfold dom_impl, empty_impl in *.
  extens ;=> k. absurds ;=> G.
  lets R: @is_empty_inv k H. typeclass.
  false R. rewrite~ in_set_st_eq.
Qed.


(* ---------------------------------------------------------------------- *)
(** update *)

(* dom *)

Lemma dom_update : forall A B i v (M:map A B),
  dom (M[i:=v]) = (dom M \u \{i}).
Proof using.
  intros. rewrite update_impl_eq.
  simpl. unfold dom_impl, union_impl, binds_impl in *.
  apply in_extens.  (* "extens" should work directly *)
  intros x. rew_set. iff R.
    case_if~.
    case_if~. destruct~ R.
Qed.

Open Scope container_scope.

Lemma dom_update_at_indom : forall A i `{IB:Inhab B} v (M:map A B),
  i \indom M ->
  dom (M[i:=v]) = dom M.
Proof using.
  introv IB H. rewrite dom_update.
  set_prove_setup true. tests*: (x = i). 
  (* --LATER: improve "set_prove" ? *)
Qed.

Arguments dom_update_at_indom [A] i [B] {IB}.

(* -- LATER: Is it needed to have the form with [index] as hyp? *)
Lemma dom_update_at_index : forall A i `{IB:Inhab B} v (M:map A B),
  index M i ->
  dom (M[i:=v]) = dom M.
Proof using.
  introv IB H. rewrite index_eq_indom in H. rewrite dom_update.
  set_prove_setup true. tests*: (x = i). 
Qed.

Arguments dom_update_at_index [A] i [B] {IB}.

(* indom *)

Lemma indom_update_eq : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  j \indom (m[i:=v]) = (j = i \/ j \indom m).
Proof using. intros. rewrite dom_update. rew_set. extens*. Qed.

Lemma indom_update_inv : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  j \indom (m[i:=v]) -> 
  (j = i \/ j \indom m).
Proof using. introv IB H. rewrite~ indom_update_eq in H. Qed.

Lemma indom_of_indom_update_at_indom : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  j \indom (m[i:=v]) -> 
  i \indom m -> 
  j \indom m.
Proof using. introv IB H F. rewrite~ indom_update_eq in H. destruct~ H. subst~. Qed.

Lemma indom_update_of_indom : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  j \indom m -> 
  j \indom (m[i:=v]).
Proof using. intros. rewrite~ indom_update_eq. Qed.

Lemma indom_update_same : forall A `{Inhab B} (m:map A B) (i:A) (v:B),
  i \indom (m[i:=v]).
Proof using. intros. rewrite~ indom_update_eq. Qed.

Hint Resolve indom_update_same. (* --TODO: move *)

(* update *)

Lemma read_update : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  (m[i:=v])[j] = (If i = j then v else m[j]).
Proof using.
 intros. rewrite update_impl_eq. simpl. unfold read_impl. case_if~.
Qed.

Lemma read_update_same : forall A `{Inhab B} (m:map A B) (i:A) (v:B),
  (m[i:=v])[i] = v.
Proof using. intros. rewrite read_update. case_if~. Qed.

Lemma read_update_neq : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  i <> j -> 
  (m[i:=v])[j] = m[j].
Proof using. intros. rewrite read_update. case_if~. Qed.

Lemma update_update : forall A i `{Inhab B} v v' (M:map A B),
  M[i:=v][i:=v'] = M[i:=v'].
Proof using.
  intros. applys fun_ext_1.
  intros k. do 3 rewrite update_impl_eq. case_if~.
Qed.


(* ---------------------------------------------------------------------- *)
(** binds *)

(* ---TODO: {Inhab B} could probably be removed below in many places,
            because [binds M i v] with [M:map A B] entails {Inhab B}. *)

Lemma binds_inj : forall A i `{Inhab B} v1 v2 (M:map A B),
  binds M i v1 -> 
  binds M i v2 -> 
  v1 = v2.
Proof using.
  introv IB H1 H2.
  rewrite (@binds_eq_indom_read A B IB) in *.
  destruct H1; destruct H2. congruence. (* --TODO: cleanup *)
Qed.

Lemma binds_of_indom_read : forall A `{Inhab B} (M:map A B) x v,
  x \indom M -> 
  M[x] = v -> 
  binds M x v.
Proof using.
  intros. rewrite~ (@binds_eq_indom_read A B H). (* why need explicit args? *)
Qed.

Lemma indom_of_binds : forall A `{Inhab B} (M:map A B) x v,
  binds M x v -> 
  x \indom M.
Proof using. introv IB K. rewrite* (@binds_eq_indom_read A B IB) in K. Qed.

Lemma index_of_binds : forall A i `{Inhab B} v (M:map A B),
  binds M i v -> 
  index M i.
Proof using. introv IB K. rewrite* (@binds_eq_indom_read A B IB) in K. Qed.

Lemma read_of_binds : forall A `{Inhab B} (M:map A B) x v,
  binds M x v -> 
  M[x] = v.
Proof using. introv K. rewrite* (@binds_eq_indom_read A B H) in K. Qed.

Lemma binds_update_neq : forall A B i j v w (M:map A B),
  i <> j -> 
  binds M i v -> 
  binds (M[j:=w]) i v.
Proof using.
  introv N K. asserts IB: (Inhab B). constructor. exists* v.
  rewrite (@binds_eq_indom_read A B IB) in *.
  rewrite~ indom_update_eq. rewrite* read_update_neq.
Qed. (* --LATER: cleanup proof *)

Lemma binds_update_same : forall A B i v (M:map A B),
  binds (M[i:=v]) i v.
Proof using.
  intros.
  asserts IB: (Inhab B). constructor. exists* v.
  rewrite (@binds_eq_indom_read A B IB) in *.
  rewrite~ indom_update_eq. rewrite* read_update_same.
Qed.

Lemma binds_update_same_inv : forall A B i v w (M:map A B),
  binds (M[i:=w]) i v -> 
  v = w.
Proof using.
  introv H.
  asserts IB: (Inhab B). constructor. exists* v.
  rewrite (@binds_eq_indom_read A B IB) in *.
  rewrite~ indom_update_eq in H. rewrite* read_update_same in H.
Qed.

Lemma binds_update_neq_inv : forall A B i j v w (M:map A B),
  binds (M[j:=w]) i v -> 
  i <> j -> 
  binds M i v.
Proof using.
  introv H N.
  asserts IB: (Inhab B). constructor. exists* v.
  rewrite (@binds_eq_indom_read A B IB) in *.
  rewrite~ indom_update_eq in H. rewrite* read_update_neq in H.
Qed.

Lemma binds_update_eq : forall A B i j v w (M:map A B),
  binds (M[j:=w]) i v = (If i = j then v = w else binds M i v).
Proof using.
  intros. applys prop_ext. iff H.
  { case_if.
    { subst. applys* binds_update_same_inv. }
    { applys* binds_update_neq_inv. } }
  { case_if.
    { subst. applys* binds_update_same. }
    { applys* binds_update_neq. } }
Qed.

Lemma binds_update_inv : forall A B i j v w (M:map A B),
  binds (M[j:=w]) i v ->
  (If i = j then v = w else binds M i v).
Proof using. introv H. rewrite~ binds_update_eq in H. Qed.


(* ---------------------------------------------------------------------- *)
(* union *)

Lemma union_read_l : forall A `{Inhab B} (m1 m2:map A B) (i:A),
  i \indom m1 ->
  dom m1 \# dom m2 ->
  m1[i] = (m1 \u m2)[i].
Proof.
  introv M D. rewrite set_disjoint_eq in D.
  simpl. unfold read_impl, union_impl. cases (m2 i).
  { false D M. applys~ indom_of_binds. simpl. unfolds* binds_impl. }
    (* --LATER: simplify line above *)
  { cases~ (m1 i). }
Qed.

Lemma union_read_r : forall A `{Inhab B} (m1 m2:map A B) (i:A),
  i \indom m2 ->
  dom m1 \# dom m2 ->
  m2[i] = (m1 \u m2)[i].
Proof.
  introv M D. rewrite set_disjoint_eq in D.
  simpl. unfold read_impl, union_impl. cases (m2 i).
  { auto. } 
  { cases (m1 i) as C.
    { false D M. applys~ indom_of_binds. simpl. unfolds* binds_impl. }
    (* --LATER: simplify line above *)
    { auto. } }
Qed.


(* ---------------------------------------------------------------------- *)
(** remove *)

Lemma dom_remove : forall A B (M:map A B) E,
  dom (M\-E) = (dom M \- E).
Proof using.
  intros. simpl. unfold remove_impl, dom_impl in *.
  apply in_extens.  (* "extens" should work directly *)
  intros x. rew_set. iff R (R1&R2); case_if~.
Qed.


(* ---------------------------------------------------------------------- *)
(** remove one *)

Lemma dom_remove_one : forall A B i (M:map A B),
  dom (M\--i) = dom M \- \{i}.
Proof using. intros. applys~ dom_remove. Qed. (* --TODO: needed ? *)

Lemma index_remove_one_in : forall A B i j (M:map A B),
  index M j -> 
  i <> j -> 
  index (M\--i) j.
Proof using.
  introv R N. rewrite index_eq_indom in *. rewrite dom_remove_one.
  rew_set. auto. (* --TODO: "rew_set*" *)
Qed.

Arguments index_remove_one_in [A] [B].

Lemma remove_one_update : forall A `{Inhab B} (m:map A B) (i:A) (v:B),
  (m[i:=v] \- \{i}) = (m \- \{i}).
Proof using.
  intros. applys fun_ext_1.
  intros k. rewrite update_impl_eq.
  simpl. unfold remove_impl. do 2 case_if~.
Qed.

Lemma read_remove_one_neq : forall A `{Inhab B} (M:map A B) i j,
  i <> j ->
  (M\--i)[j] = M[j].
Proof using.
  introv N. simpl. unfold remove_impl, read_impl. case_if~.
Qed.

Lemma update_remove_one_neq : forall A B (M:map A B) i j v,
  i <> j ->
  (M\--i)[j:=v] = (M[j:=v] \--i).
Proof using.
  introv N. applys fun_ext_1.
  intros k. do 2 rewrite update_impl_eq.
  simpl. unfold remove_impl. do 2 case_if~.
Qed.


(* ---------------------------------------------------------------------- *)
(** restrict *)

Lemma restrict_single : forall A (x:A) `{Inhab B} (M:map A B),
  x \indom M ->
  M \| \{x} = (x \:= (M[x])).
Proof using.
  introv N. applys fun_ext_1.
  intros k. simpls. unfolds dom_impl, restrict_impl, single_bind_impl, read_impl.
  rew_set in *. do 2 case_if~. subst. destruct (M x); auto_false.
Qed.


(* ---------------------------------------------------------------------- *)
(** structural decomposition *)

Lemma eq_union_restrict_remove : forall A (E:set A) B (M:map A B),
  M = (M \- E) \u (M \| E).
Proof using.
  intros. applys fun_ext_1.
  intros k. simpls. unfolds remove_impl, restrict_impl, union_impl.
  case_if~. destruct~ (M k).
Qed.

Lemma eq_union_restrict_remove_one : forall A (x:A) B `{Inhab B} (M:map A B),
  x \indom M ->
  M = (M \- \{x}) \u (x \:= (M[x])).
Proof using.
  intros. rewrite~ <- restrict_single. apply eq_union_restrict_remove.
Qed.


(* ---------------------------------------------------------------------- *)
(** fold *)

Lemma fold_empty : forall A B C (m:monoid_op C) (f:A->B->C),
  fold m f (\{}:map A B) = monoid_neutral m.
Proof using.
  intros. rewrite fold_eq_fold_pairs.
  match goal with |- context [ set_st ?X] =>
    cuts_rewrite (set_st X = \{}) end.
  rewrite~ fold_empty.
  rew_set. intros [k x]. rew_set. iff (?&?&M&N) ?; tryfalse.
Qed.

Lemma fold_single : forall A B C (m:monoid_op C) (f:A->B->C) (k:A) (x:B),
  Monoid m ->
  fold m f (k\:=x) = f k x.
Proof using.
  intros. rewrite fold_eq_fold_pairs.
  match goal with |- context [ set_st ?X] =>
    cuts_rewrite (set_st X = \{(k,x)}) end.
  rewrite~ fold_single.
  rew_set. intros [k' x']. rew_set. iff (?&?&E&R) M.
    inverts E. hnf in R. simpls. unfolds single_bind_impl.
     case_if~. inverts~ R. subst~.
    inverts M. unfolds binds_impl. simpls. unfolds single_bind_impl.
     exists k x. splits~. case_if~.
Qed.

(* internal use *)
Lemma binds_impl_dom_impl : forall A `{Inhab B} (M:map A B) x v,
  binds_impl M x v -> 
  x \in dom_impl M.
Proof using. introv IB K. unfolds binds_impl, dom_impl. rew_set. congruence. Qed.

(* --LATER: avoid `{Inhab B}: if not empty, then inhab, else result true *)
(* internal use *)
Lemma finite_to_finite_fold_support : forall A `{Inhab B} (M:map A B),
  finite M ->
  LibSet.finite
    \set{ p | exists k x, p = (k, x) /\ binds_impl M k x}.
Proof using.
  introv IB HM. lets (L&E): finite_inv_list_covers HM.
  applys finite_of_list_covers (LibList.map (fun x => (x, M[x])) L).
  intros (k',x') Hk. rew_set. destruct Hk as (k&x&EQ&R). inverts EQ.
  forwards~: binds_impl_dom_impl R. forwards~ V: E k.
  lets U: LibList.mem_map (fun x => (x, M[x])) V. applys_eq U 2.
  simpl. unfold read_impl. hnf in R. rewrite~ R.
Qed.

(* --LATER: avoid `{Inhab B} *)
Lemma fold_union : forall A `{Inhab B} C (m:monoid_op C) (f:A->B->C) (M N : map A B),
  Comm_monoid m ->
  finite M ->
  finite N -> 
  M \# N ->
  fold m f (M \u N) = monoid_oper m (fold m f M) (fold m f N).
Proof using.
  introv IB Hm FM FN HD. do 3 rewrite fold_eq_fold_pairs.
  match goal with |- context [ set_st ?X] =>
    cuts_rewrite (set_st X =
       \set{ p | exists k x, p = (k, x) /\ binds_impl M k x}
    \u \set{ p | exists k x, p = (k, x) /\ binds_impl N k x}) end.
  rewrite~ fold_union.
    apply~ finite_to_finite_fold_support.
    apply~ finite_to_finite_fold_support.
    rewrite disjoint_eq. (* --TODO: applys disjoint_prove. *)
    intros (k,x). rew_set. intros (k1&x1&E1&R1) (k2&x2&E2&R2).
     inverts E1. forwards~: binds_impl_dom_impl R1.
     inverts E2. forwards~: binds_impl_dom_impl R2.
     applys* @disjoint_inv HD. typeclass.
  rew_set. intros (k',x'). rew_set. iff (k&x&E&F) H.
    inverts E. simpl in F. unfolds union_impl, binds_impl. cases (N k).
      right. exists k x. inverts~ F.
      left. exists k x. auto.
    simpl. destruct H as [(k&x&E&R)|(k&x&E&R)].
      inverts E. exists k x. split~. forwards~: binds_impl_dom_impl R.
       cases (N k) as EN.
         false. applys~ @disjoint_inv k HD. typeclass.
          unfold dom_impl. rew_set. congruence.
         unfolds union_impl, binds_impl. rewrite~ EN.
      inverts E. exists k x. split~. forwards~: binds_impl_dom_impl R.
        unfolds union_impl, binds_impl. rewrite~ R.
Qed. (* --TODO: cleanup proof *)

End Properties.


(* -- LATER: equivalent definition of fold
  Lemma fold_def_dom : forall A `{Inhab B} C (m:monoid_def C) (f:A->B->C) (M:map A B),
    fold m f M = LibContainer.fold m (fun k => f k (M[k])) (dom M).
    - E = dom M
    - repr L E
    - fold f (map i E) = fold (fun x => f (i x)) E
    - i = fun x => (x, M[x])
    - injective i -> repr E L -> repr (LibSet.map i E) (LibList.map i L)
    - injective i -> No_duplicates L -> No_duplicates (map i L)
    - repr E L -> repr E L' -> fold f E = fold f L'
*)


(* ---------------------------------------------------------------------- *)
(** rewriting *)

(** EXPERIMENTAL -- beavior of [rew_map] might change

    The challenge is that it is not clear what we want to do facing
    a read at index [i] on an update at index [j], when it is not obvious
    from the context whether [i] and [j] might be equal. Often, it is
    desirable to introduce a case analysis, but there are cases where
    one would like to assume that if [i] and [j] are syntactically different,
    i.e. one has not been already substituted for the other, then we wish
    to issue a subgoal [i<>j]. *)

Hint Rewrite @indom_update_eq @read_update_neq @read_update_same : rew_map.

Tactic Notation "rew_map" :=
  autorewrite with rew_map.
Tactic Notation "rew_map" "in" hyp(H) :=
  autorewrite with rew_map in H.
Tactic Notation "rew_map" "in" "*" :=
  autorewrite_in_star_patch ltac:(fun tt => autorewrite with rew_map).
  (* autorewrite with rew_map in *. *)
Tactic Notation "rew_map" "~" :=
  rew_map; auto_tilde.
Tactic Notation "rew_map" "*" :=
   rew_map; auto_star.
Tactic Notation "rew_map" "~" "in" hyp(H) :=
  rew_map in H; auto_tilde.
Tactic Notation "rew_map" "*" "in" hyp(H) :=
  rew_map in H; auto_star.


(* ---------------------------------------------------------------------- *)
(** ** Structural properties *)

Section Instances.
Variables (A B:Type).

Transparent map empty_inst single_bind_inst binds_inst
 union_inst dom_inst disjoint_inst.

Global Instance map_union_empty_l : Union_empty_l (T:=map A B).
Proof using.
  constructor. intros m. simpl.
  unfold union_impl, empty_impl, map. extens.
  intros x. destruct~ (m x).
Qed.

Global Instance map_union_assoc : Union_assoc (T:=map A B).
Proof using.
  constructor. intros M N P. simpl.
  unfold union_impl, map. extens.
  intros k. destruct~ (P k).
Qed.

End Instances.


(* ---------------------------------------------------------------------- *)
(** ** Remark *)

(* The following lemma is actually not used, because [discriminate] does the
   job. Perhaps this will fail someday if [binds] becomes really opaque?

  Goal
    forall A B a b,
    binds (\{} : map A B) a b ->
    False.
  Proof using.
    intros. discriminate.
  Qed.
*)



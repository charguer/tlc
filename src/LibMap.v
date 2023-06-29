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

Definition incl_impl M N :=
  forall k v, M k = Some v -> N k = Some v.
  (* same as:
     forall k,
     match M k with
     | None => True
     | Some v => N k = Some v
     end. *)

End Operations.

Definition read_impl A `{Inhab B} (M:map A B) (k:A) :=
  match M k with
  | None => arbitrary
  | Some v => v
  end.

Definition fold_impl A B C (m:monoid_op C) (f:A->B->C) (M:map A B) :=
  LibContainer.fold m (fun p => let '(a,b) := p in f a b)
    (\set{ p | exists k x, p = (k, x) /\ binds_impl M k x }).

(* LATER: a typeclass for filter? *)
Definition filter A B (F:A->B->Prop) (f:map A B) : map A B :=
  fun (x:A) => match f x with
    | None => None
    | Some y => If F x y then Some y else None
    end.

(* LATER: a typeclass for map? *)
Definition map_ A B1 B2 (F:A->B1->B2) (f:map A B1) : map A B2 :=
  fun (x:A) => match f x with
    | None => None
    | Some y => Some (F x y)
    end.


(* ---------------------------------------------------------------------- *)
(** ** Notation through typeclasses *)

#[global]
Instance empty_inst : forall A B, BagEmpty (map A B).
  constructor. rapply (@empty_impl A B). Defined.

#[global]
Instance single_bind_inst : forall A B, BagSingleBind A B (map A B).
  constructor. rapply (@single_bind_impl A B). Defined.

#[global]
Instance binds_inst : forall A B, BagBinds A B (map A B).
  constructor. rapply (@binds_impl A B). Defined.

#[global]
Instance union_inst : forall A B, BagUnion (map A B).
  constructor. rapply (@union_impl A B). Defined.

#[global]
Instance incl_inst : forall A B, BagIncl (map A B).
  constructor. rapply (@incl_impl A B). Defined.

#[global]
Instance remove_inst : forall A B, BagRemove (map A B) (set A).
  constructor. rapply (@remove_impl A B). Defined.

#[global]
Instance restrict_inst : forall A B, BagRestrict (map A B) (set A).
  constructor. rapply (@restrict_impl A B). Defined.

#[global]
Instance read_inst : forall A `{Inhab B}, BagRead A B (map A B).
  constructor. rapply (@read_impl A B H). Defined.

#[global]
Instance dom_inst : forall A B, BagDom (map A B) (set A).
  constructor. rapply (@dom_impl A B). Defined.

#[global]
Instance disjoint_inst : forall A B, BagDisjoint (map A B).
  constructor. rapply (@disjoint_impl A B). Defined.

#[global]
Instance index_inst : forall A B, BagIndex A (map A B).
  constructor. rapply (@index_impl A B). Defined.

#[global]
Instance fold_inst : forall A B C, BagFold C (A->B->C) (map A B).
  constructor. rapply (@fold_impl A B C). Defined.

Global Opaque map empty_inst dom_inst single_bind_inst binds_inst
 union_inst incl_inst restrict_inst remove_inst read_inst
 dom_inst disjoint_inst index_inst fold_inst.

#[global]
Instance Inhab_map : forall A B, Inhab (map A B).
Proof using. intros. apply (Inhab_of_val (@empty_impl A B)). Qed.


(* Note: we may check that [update] is derivable via [bag_update_as_union_single]
      Instance update_inst : forall A B, BagUpdate A B (map A B).
      Proof. typeclass. Qed.
*)

(* ---------------------------------------------------------------------- *)
(** ** TEMPORARY *)

(*-- LATER: make [finite] a typeclass, define [finite_impl]
     using [dom_impl], and prove a lemma [finite_eq] of type
     [finite M = finite (dom M)]. *)

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

(* only for internal use *)
Lemma indom_eq_app_neq_none : forall A B (M:map A B) k,
  k \indom M = (M k <> None).
Proof using. auto. Qed.

(* only for internal use *)
Lemma indom_inv_app_neq_none : forall A B (M:map A B) k,
  k \indom M ->
  (M k <> None).
Proof using. auto. Qed.


End Reformulation.


(* ********************************************************************** *)
(** * Properties of maps *)
(* -- TODO: under construction *)

Section Properties.
Transparent map empty_inst single_bind_inst binds_inst
 union_inst restrict_inst remove_inst read_inst
 dom_inst disjoint_inst index_inst fold_inst.

Hint Extern 1 (Some _ <> None) => congruence.
Hint Extern 1 (None <> Some _) => congruence.

(* ---------------------------------------------------------------------- *)
(** extens *)

Lemma extensionality : forall A B (IB:Inhab B) (M1 M2:map A B),
  (forall (k:A), k \indom M1 <-> k \indom M2) ->
  (forall (k:A), k \indom M1 -> M1[k] = M2[k]) ->
  M1 = M2.
Proof using.
  introv HD HE. extens. intros k.
  specializes HD k. specializes HE k.
  unfold dom_inst, dom_impl, read_inst, read_impl in *. simpls.
  repeat rewrite in_set_st_eq in *.
  case_eq (M1 k); introv Hv1; rewrite Hv1 in HE,HD;
  case_eq (M2 k); introv Hv2; try rewrite Hv2 in HE,HD.
  { forwards* ->: HE. }
  { false. forwards: (proj1 HD); auto_false. }
  { false. forwards: (proj2 HD); auto_false. }
  { auto. }
Qed.

Lemma extensionality_of_dom_eq : forall A B (IB:Inhab B) (M1 M2:map A B),
  (dom M1 = dom M2) ->
  (forall (k:A), k \indom M1 -> M1[k] = M2[k]) ->
  M1 = M2.
Proof using. introv E Hk. applys extensionality. { rewrite* E. } { applys Hk. } Qed.

(* See also sections "prove same" and "prove empty" *)


(* ---------------------------------------------------------------------- *)
(** index *)

Lemma index_of_indom : forall A B (M:map A B) k,
  k \indom M ->
  index M k.
Proof using. intros. rewrite~ index_eq_indom. Qed.


(* ---------------------------------------------------------------------- *)
(** dom *)

Section Dom.
Transparent dom_inst incl_inst.

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

Lemma dom_remove : forall A B (M : map A B) (E : set A),
  dom (M \- E) = dom M \- E.
Proof using.
  intros. simpl. unfold dom_impl, remove_impl.
  rew_set. intros x. rew_set. iff R; case_if*.
Qed.

Lemma dom_restrict : forall A B (M : map A B) (E : set A),
  dom (M \| E) = dom M \n E.
Proof using.
  intros. simpl. unfold dom_impl, restrict_impl.
  rew_set. intros x. rew_set. iff R; case_if*.
Qed.

Lemma dom_map : forall A B (IB:Inhab B) C (f:A->B->C) M,
  dom (map_ f M) = dom M.
Proof using.
  intros. simpl. unfold dom_impl, map_.
  rew_set. intros x. rew_set. destruct (M x); iff*.
Qed.

Lemma dom_filter : forall A B (IB:Inhab B) (f:A->B->Prop) M,
  dom (filter f M) \c dom M.
Proof using.
  intros. simpl. unfold dom_impl, filter.
  rew_set. intros x. rew_set. destruct* (M x).
Qed.

Lemma dom_incl : forall A B (M N : map A B),
  M \c N ->
  dom M \c dom N.
Proof using.
  introv. simpl. unfold dom_impl, incl_inst, incl_impl.
  rew_set. intros HI x Hx. rew_set in *. specializes HI x.
  destruct (M x) as [v|]; tryfalse.
  specializes HI v. destruct (N x) as [v'|]; auto_false*.
Qed.

End Dom.


(* ---------------------------------------------------------------------- *)
(** finite *)

Lemma finite_empty : forall A B,
  finite (\{} : map A B).
Proof using.
  intros. unfold finite. rewrite dom_empty. apply finite_empty.
Qed.

Lemma finite_single : forall A B (k : A) (x : B),
  finite (k\:=x).
Proof using.
  intros. unfold finite. rewrite dom_single. apply finite_single.
Qed.

Lemma finite_union_eq : forall A B (M N : map A B),
  finite (M \u N) = (finite M /\ finite N).
Proof using.
  intros. unfold finite. rewrite dom_union. apply finite_union_eq.
Qed.

Lemma finite_union : forall A B (M N : map A B),
  finite M ->
  finite N ->
  finite (M \u N).
Proof using. intros. rewrite* finite_union_eq. Qed.

Lemma finite_union_inv : forall A B (M N : map A B),
  finite (M \u N) ->
  finite M /\ finite N.
Proof using. introv H. rewrite* finite_union_eq in H. Qed.

Lemma finite_remove : forall A B (M : map A B) (E : set A),
  finite M ->
  finite (M \- E).
Proof using.
  introv. unfold finite. rewrite dom_remove. apply finite_remove.
Qed.

Lemma finite_restrict : forall A B (M : map A B) (E : set A),
  finite M ->
  finite (M \| E).
Proof using.
  introv. unfold finite. rewrite dom_restrict. apply finite_inter_l.
Qed.

Lemma finite_incl : forall A B (M N : map A B),
  M \c N ->
  finite N ->
  finite M.
Proof using.
  introv HI HM. unfold finite. lets HD: dom_incl HI. applys* finite_incl.
Qed.


(* ---------------------------------------------------------------------- *)
(** indom *)

Lemma indom_empty_eq : forall A B x,
  x \indom (\{}:map A B) = False.
Proof using.
  intros. rewrite dom_empty. rewrite in_empty_eq. auto.
Qed.

Lemma indom_empty_inv : forall A B (x:A),
  x \indom (\{} : map A B) ->
  False.
Proof using. introv M. rewrite indom_empty_eq in M. auto. Qed.

Lemma indom_single_eq : forall A B (x1 x2:A) (v:B),
  x2 \indom (x1\:=v) = (x1 = x2).
Proof using.
  intros. rewrite dom_single. rewrite in_single_eq. extens*.
Qed.

Lemma indom_union_eq : forall A B (IB:Inhab B) (M1 M2:map A B) x,
  x \indom (union M1 M2) = (x \indom M1 \/ x \indom M2).
Proof using.
  intros. rewrite dom_union. rewrite in_union_eq. auto.
Qed.


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

Lemma eq_empty_of_not_indom : forall A B (IB:Inhab B) (M:map A B),
  (forall x, ~ x \indom M) ->
  M = \{}.
Proof using.
  introv IB H. applys extensionality.
  { intros x. rewrite indom_empty_eq. iff*. }
  { intros x Dx. false* H. }
Qed.


(* ---------------------------------------------------------------------- *)
(** single *)

Lemma read_single : forall A B (IB:Inhab B) (k:A) (x:B),
  (k \:= x)[k] = x.
Proof using.
  intros. unfold read, read_inst, read_impl.
  unfold single_bind, single_bind_inst, single_bind_impl.
  case_if*.
Qed.

(* ---------------------------------------------------------------------- *)
(** disjoint *)

Lemma disjoint_eq_not_indom_both : forall A B (M1 M2:map A B),
  disjoint M1 M2 = (forall k, k \indom M1 -> k \indom M2 -> False).
Proof using.
  extens. unfold disjoint_impl. rewrite* set_disjoint_eq.
Qed.

Lemma disjoint_of_not_indom_both : forall A B (M1 M2:map A B),
  (forall k, k \indom M1 -> k \indom M2 -> False) ->
  disjoint M1 M2.
Proof using. introv M. rewrite~ disjoint_eq_not_indom_both. Qed.

Lemma disjoint_inv_not_indom_both : forall A B (M1 M2:map A B) k,
  disjoint M1 M2 ->
  k \indom M1 ->
  k \indom M2 ->
  False.
Proof using. introv. rewrite* disjoint_eq_not_indom_both. Qed.

Lemma disjoint_single_of_not_indom : forall A B (M:map A B) x (v:B),
  ~ x \indom M ->
  disjoint (x\:=v) M.
Proof using.
  introv N. unfold disjoint, disjoint_inst, disjoint_impl.
  unfold single_bind, single_bind_inst, single_bind_impl, dom_impl.
  rewrite set_disjoint_eq. intros x'.
  repeat rewrite in_set_st_eq. case_if; subst; auto_false.
Qed.

Lemma not_indom_of_indom_disjoint : forall A B (M1 M2:map A B) x,
  x \indom M1 ->
  disjoint M1 M2 ->
  ~ x \indom M2.
Proof using.
  introv H1 D H2. rewrite* disjoint_eq_not_indom_both in D.
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
  intros k. do 3 rewrite update_impl_eq. case_if*.
Qed.

(* update same *)

Lemma update_same : forall A B (IA:Inhab B) (M:map A B) (x:A),
  x \indom M ->
  M[x:=M[x]] = M.
Proof using.
  introv Dx. applys extensionality.
  { intros k. rewrite* dom_update_at_indom. }
  { intros k Hk. rewrite* dom_update_at_indom in Hk.
    rewrite read_update. case_if*. subst*. }
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
(** incl *)

Section Incl.
Transparent read_inst incl_inst.

Lemma read_incl : forall A B (IB:Inhab B) (M N:map A B) i,
  i \indom M ->
  M \c N ->
  N[i] = M[i].
Proof using.
  introv Hi HI. simpls. unfolds read_impl, incl_impl, dom_impl.
  rew_set in *. specializes HI i. destruct (N i) as [v|].
  { destruct (M i) as [w|]; tryfalse. specializes HI w __. inverts* HI. }
  { destruct (M i) as [w|]; tryfalse. specializes HI w __. inverts* HI. }
Qed.

End Incl.

(* ---------------------------------------------------------------------- *)
(* union *)

(* TODO: this is convenient, though it reveals non commutativity.
   TODO: change the priority of the union: left argument should be read first *)

Lemma read_union_cases : forall A B (IB:Inhab B) (M1 M2:map A B) x,
  read (union M1 M2) x = (If x \indom M2 then M2[x] else M1[x]).
Proof using.
  intros. unfold read, read_inst, read_impl.
  unfold dom, dom_inst, dom_impl. rewrite in_set_st_eq.
  unfold union, union_inst, union_impl.
  case_eq (M2 x); introv Hv2; case_if; congruence.
Qed.

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

Section Restrict.
Transparent read_inst incl_inst restrict_inst.

Lemma restrict_single : forall A (x:A) `{Inhab B} (M:map A B),
  x \indom M ->
  M \| \{x} = (x \:= (M[x])).
Proof using.
  introv N. applys fun_ext_1.
  intros k. simpls. unfolds dom_impl, restrict_impl, single_bind_impl, read_impl.
  rew_set in *. do 2 case_if~. subst. destruct (M x); auto_false.
Qed.

Lemma restrict_incl : forall A B (M N : map A B),
  M \c N ->
  N \| (dom M) = M.
Proof using.
  introv HI. applys fun_ext_1. simpls. intros k.
  unfolds dom_impl, restrict_impl, read_impl, incl_impl.
  specializes HI k. rew_set. case_if*.
  { destruct (M k) as [v|]; tryfalse. applys* HI. }
Qed.

End Restrict.


(* ---------------------------------------------------------------------- *)
(** map *)

Lemma indom_map_eq : forall A B C (IB:Inhab B) (f:A->B->C) M x,
  x \indom (map_ f M) = x \indom M.
Proof using. intros. rewrite* dom_map. Qed.

Lemma indom_map : forall A B C (IB:Inhab B) (f:A->B->C) M x,
  x \indom M ->
  x \indom (map_ f M).
Proof using. introv IB H. rewrite* indom_map_eq. Qed.

Lemma indom_map_inv : forall A B C (IB:Inhab B) (f:A->B->C) M x,
  x \indom (map_ f M) ->
  x \indom M.
Proof using. introv IB H. rewrite* indom_map_eq in H. Qed.

Lemma read_map : forall A B C (IB:Inhab B) (IC:Inhab C) (f:A->B->C) M x,
  x \indom M ->
  (map_ f M)[x] = f x (M[x]).
Proof using.
  introv Hx. (* --TODO bug? rewrite @indom_eq_app_neq_none in M. ; also further on *)
  lets Hx': indom_inv_app_neq_none (rm Hx).
  unfold map_. simpls. unfolds read_impl.
  destruct (M x); auto_false.
Qed.

Lemma map_empty : forall A B C (IB:Inhab B) (f:A->B->C),
  map_ f ((\{} : map A B)) = empty.
Proof using. auto. Qed.

Lemma map_single : forall A B C (IB:Inhab B) (IC:Inhab C) (f:A->B->C) x y,
  map_ f (x \:= y) = (x \:= f x y).
Proof using.
  intros. applys extensionality_of_dom_eq.
  { rewrite dom_single. repeat rewrite* dom_map. rewrite* dom_single. }
  { intros k Hk. rewrite* dom_map in Hk.
    lets Hk': Hk. rewrite* dom_single in Hk'. rew_set in Hk'. subst x.
    repeat rewrite* (@read_map A B C IB).
    do 2 rewrite read_single. auto. }
Qed.

Lemma map_union : forall A B C (IB:Inhab B) (IC:Inhab C) (f:A->B->C) M1 M2,
  map_ f (M1 \u M2) = (map_ f M1) \u (map_ f M2).
Proof using.
  intros. applys extensionality_of_dom_eq.
  { rewrite dom_union. repeat rewrite* dom_map. rewrite* dom_union. }
  { intros k Hk. rewrite* dom_map in Hk.
    lets Hk': Hk. rewrite* dom_union in Hk'. rew_set in Hk'.
    repeat rewrite* (@read_map A B C IB).
    repeat rewrite read_union_cases. rewrite* dom_map.
    case_if.
    { rewrite* (@read_map A B C IB). }
    { rewrite* (@read_map A B C IB). } }
Qed.

Lemma map_id : forall A B (IB:Inhab B) (f:A->B->B) M,
  (forall x y, x \indom M -> y = M[x] -> f x y = y) ->
  map_ f M = M.
Proof using.
  intros. applys extensionality_of_dom_eq.
  { rewrite* dom_map. }
  { intros k Hk. rewrite* dom_map in Hk. rewrite* (@read_map A B B IB). }
Qed.

Hint Rewrite indom_map map_empty map_single map_union : rew_map.


(* ---------------------------------------------------------------------- *)
(** filter *)

Lemma read_filter : forall A B (IB:Inhab B) (f:A->B->Prop) M x,
  x \indom M ->
  f x (M[x]) ->
  (filter f M)[x] = M[x].
Proof using.
  introv Hx. lets Hx': indom_inv_app_neq_none (rm Hx).
  unfold filter. simpls. unfolds read_impl.
  destruct (M x); auto_false. case_if*.
Qed.

(* indom *)

Lemma indom_filter_eq : forall A B (IB:Inhab B) (f:A->B->Prop) M x,
  x \indom (filter f M) = (x \indom M /\ f x (M[x])).
Proof using.
  intros. simpl. unfold dom_impl, filter, read_impl. rew_set.
  extens. destruct* (M x). { case_if; auto_false*. }
Qed.

Lemma indom_filter : forall A B (IB:Inhab B) (f:A->B->Prop) M x,
  x \indom M ->
  f x (M[x]) ->
  x \indom (filter f M).
Proof using. intros. rewrite* (@indom_filter_eq A B IB). Qed.

Lemma indom_filter_inv : forall A B (IB:Inhab B) (f:A->B->Prop) M x,
  x \indom (filter f M) ->
  x \indom M /\ f x (M[x]) /\ (filter f M)[x] = M[x].
Proof using. introv H. hint read_filter. rewrite* (@indom_filter_eq A B IB) in H. Qed.

(* Filter special *)

Lemma filter_none : forall A B (IB:Inhab B) (f:A->B->Prop) M,
  (forall x, x \indom M -> ~ f x (M[x])) ->
  filter f M = empty.
Proof using.
  introv H. symmetry. applys extensionality.
  { intros k. rewrite dom_empty. rew_set. iff R; tryfalse.
    forwards* (Hk&Hfk&_): indom_filter_inv R. }
  { intros k. rewrite dom_empty. rew_set. auto_false. }
Qed.

Lemma filter_all : forall A B (IB:Inhab B) (f:A->B->Prop) M,
  (forall x, x \indom M -> f x (M[x])) ->
  filter f M = M.
Proof using.
  introv H. symmetry. applys extensionality.
  { intros k. rewrite (@indom_filter_eq A B IB). iff*. }
  { intros k Hk. rewrite* read_filter. }
Qed.

Lemma filter_idempotent : forall A B (IB:Inhab B) (f:A->B->Prop) M,
  filter f (filter f M) = filter f M.
Proof using.
  introv IB. symmetry. applys extensionality.
  { intros k. repeat rewrite (@indom_filter_eq A B IB). iff* (Hk&Hfk).
    { split*. rewrite* read_filter. } }
  { intros k Hk. lets (?&?&?): indom_filter_inv Hk.
    repeat rewrite* read_filter. }
Qed.

Lemma filter_swap : forall A B (IB:Inhab B) (f1 f2:A->B->Prop) M,
  filter f1 (filter f2 M) = filter f2 (filter f1 M).
Proof using.
  introv IB. intros. applys extensionality.
  { intros k. repeat rewrite (@indom_filter_eq A B IB). iff* ((Hk&Hfka)&Hfkb).
    { rewrite* read_filter in Hfkb. repeat split*. rewrite* read_filter. }
    { rewrite* read_filter in Hfkb. repeat split*. rewrite* read_filter. } }
  { intros k Hk. lets (Hk'&E&?): indom_filter_inv Hk. lets (Hk''&?&?): indom_filter_inv Hk'.
    rewrite* read_filter in E. repeat rewrite* read_filter. applys* indom_filter. }
Qed.

Lemma filter_incompatible : forall A B (IB:Inhab B) (f1 f2:A->B->Prop) M,
  (forall x y, x \indom M -> y = M[x] -> f1 x y -> f2 x y -> False) ->
  filter f1 (filter f2 M) = empty.
Proof using.
  introv R. applys filter_none. intros k Hk Hf1.
  lets (Hk'&Hf2&E): indom_filter_inv Hk.
  rewrite* read_filter in Hf1.
Qed.

Lemma filter_partition : forall A B (IB:Inhab B) (f1 f2:A->B->Prop) M M1 M2,
  (forall x y, x \indom M -> y = M[x] -> f1 x y = ~ (f2 x y)) ->
  M1 = filter f1 M ->
  M2 = filter f2 M ->
  M = union M1 M2 /\ disjoint M1 M2.
Proof using.
  introv HP -> ->. split.
  { unfold read, read_inst, read_impl in *.
    unfold union, union_inst, union_impl, dom, dom_inst, dom_impl, filter in *.
    extens. intros k. specializes HP k. rew_set in HP.
    gen HP. destruct* (M k). intros N. specializes N b.
    case_if*. case_if*. rewrite N in *; eauto. false*. }
  { applys disjoint_of_not_indom_both. intros k Hk1 Hk2.
    lets (?&?&?): indom_filter_inv Hk1.
    lets (?&?&?): indom_filter_inv Hk2. rewrite HP in *; eauto. }
Qed.

(* Filter on operations *)

Lemma filter_empty: forall A B {IB:Inhab B} (f:A->B->Prop),
  filter f empty = empty.
Proof using .
  intros. applys filter_none. intros x K.
  rewrite* indom_empty_eq in K.
Qed.

Lemma filter_single : forall A B (IB:Inhab B) (f:A->B->Prop) x y,
    filter f (x \:= y)
  = If f x y then (x \:= y) else empty.
Proof using.
  intros. case_if.
  { applys filter_all. intros k K. rewrite indom_single_eq in K.
    subst. rewrite* read_single. }
  { applys filter_none. intros k K. rewrite indom_single_eq in K.
    subst. rewrite* read_single. }
Qed.

Lemma filter_union : forall A B (IB:Inhab B) (f:A->B->Prop) M1 M2,
  disjoint M1 M2 ->
  filter f (M1 \u M2) = (filter f M1) \u (filter f M2).
Proof using.
  introv IB D. extens. intros x.
  unfold disjoint, disjoint_inst, disjoint_impl, dom, dom_inst, dom_impl in D.
  rew_set in D. specializes D x. rew_set in D.
  unfold union, union_inst, union_impl, filter.
  cases (M2 x); cases (M1 x); try solve [ auto | case_if* ]. false* D.
Qed.
(* beginning of longer higher-level proof:
  introv IB D. symmetry. applys extensionality.
  { intros k. rewrite dom_union. rew_set. iff R; tryfalse.
    rewrite (@indom_filter_eq A B IB). rewrite dom_union. rew_set.
    rewrite read_union_cases. destruct R as [R|R].
    { lets (?&?&?): indom_filter_inv R. splits*. case_if*.
      false* disjoint_inv_not_indom_both. }
*)

Hint Rewrite filter_empty filter_single filter_union : rew_map.


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
  lets U: LibList.mem_map (fun x => (x, M[x])) V. applys_eq U.
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

Lemma fold_induction :
  forall A B (IB:Inhab B) C (m : monoid_op C) (f : A -> B -> C) (P : C -> Prop) (M : map A B),
  Comm_monoid m ->
  P (monoid_neutral m) ->
  (forall x i, P x -> P (monoid_oper m (f i (M[i])) x)) ->
  finite M ->
  P (fold m f M).
Proof using.
  introv Hm Hbase Hstep Hfinite. rewrite fold_eq_fold_pairs.
  apply* fold_induction.
  { intros x (i,v) Hx Px. rew_set in Hx. destruct Hx as (i'&v'&E&HB).
    inverts E. rewrite <- (read_of_binds HB). applys* Hstep. }
  { applys* finite_to_finite_fold_support. }
Qed.


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

#[global]
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



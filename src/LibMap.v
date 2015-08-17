(**************************************************************************
* TLC: A library for Coq                                                  *
* Finite maps                                                             *
**************************************************************************)

(* FILE UNDER CONSTRUCTION *)

Set Implicit Arguments.
Generalizable Variables A B.
Require Import LibTactics LibLogic LibReflect LibOption
  LibRelation LibLogic LibOperation LibEpsilon LibSet.
Require Export LibBag.


(* ---------------------------------------------------------------------- *)
(** ** Notations to help the typechecker *)

Notation "x \indom E" := (x \in (dom E : set _)) 
  (at level 39) : container_scope.
Notation "x \notindom E" := (x \notin ((dom E) : set _)) 
  (at level 39) : container_scope.


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

Definition empty_impl : map A B := fun _ => None.
Definition single_bind_impl k x := fun k' => If k = k' then Some x else None.
Definition binds_impl M k x := M k = Some x.
Definition union_impl M N := 
  fun k => match N k with
           | None => M k
           | Some v => Some v
           end.
Definition remove_impl M E :=
  fun k => If k \in E then None else M k.
Definition restrict_impl M E :=
  fun k => If k \in E then M k else None.

End Operations.

Definition read_impl A `{Inhab B} (M:map A B) (k:A) :=
  match M k with
  | None => arbitrary
  | Some v => v
  end.

(* ---------------------------------------------------------------------- *)
(** ** Notation through typeclasses *)

Instance empty_inst : forall A B, BagEmpty (map A B).
  constructor. rapply (@empty_impl A B). Defined.
Instance single_bind_inst : forall A B, BagSingleBind A B (map A B).
  constructor. rapply (@single_bind_impl A B). Defined.
Instance binds_inst : forall A B, BagBinds A B (map A B). 
  constructor. rapply (@binds_impl A B). Defined.
Instance union_inst : forall A B, BagUnion (map A B). (* todo: bug pas si on enlve B *)
  constructor. rapply (@union_impl A B). Defined.
Instance remove_inst : forall A B, BagRemove (map A B) (set A).
  constructor. rapply (@remove_impl A B). Defined.
Instance restrict_inst : forall A B, BagRestrict (map A B) (set A).
  constructor. rapply (@restrict_impl A B). Defined.
Instance read_inst : forall A `{Inhab B}, BagRead A B (map A B).
  constructor. rapply (@read_impl A B H). Defined.

(* bin : check
Instance update_inst : forall A B, BagUpdate A B (map A B).
typeclass.
*)

Global Opaque map empty_inst single_bind_inst binds_inst
 union_inst restrict_inst remove_inst read_inst.

(** [dom] *)

Definition dom_impl A B (M:map A B) := set_st (fun k => exists v, binds M k v).

Instance dom_inst : forall A B, BagDom (map A B) (set A).
  constructor. rapply (@dom_impl A B). Defined.

Instance disjoint_inst : forall A B, BagDisjoint (map A B).
  constructor. rapply (fun M N : map A B => disjoint (dom M) (dom N)). Defined.

Instance map_inhab : forall A, Inhab (map A B).
Proof using. intros. apply (prove_Inhab (@empty_impl A B)). Qed.

Global Opaque dom_inst disjoint_inst.


(** [index] *)

Instance map_index : forall A B, BagIndex A (map A B).
Proof using. intros. constructor. exact (fun m k => k \in (dom m : set A)). Defined.

Lemma map_index_def : forall A B (m:map A B) k,
  index m k = (k \in (dom m : set A)).
Proof using. auto. Qed. 

Global Opaque map_index_def.

(* TODO: missing a lemma for extensional equality *)

(* ********************************************************************** *)
(** * Properties of maps *)
(*TODO: under construction *)

Section Properties.
Transparent map dom_inst binds_inst empty_inst.

Lemma dom_empty : forall A B,
  dom (\{} : map A B) = (\{} : set A).
Proof using.
  intros. simpl. unfold dom_impl. simpl. unfold binds_impl, empty_impl.
  apply set_ext. intros x. rewrite in_set_st_eq. iff [v Hv] H; false.
Qed.

Lemma in_dom_empty : forall A B x,
  x \indom (\{} : map A B) ->
  False.
Proof using.
  intros. rewrite dom_empty in *. eapply in_empty; typeclass.
Qed.

Lemma no_binds_empty : forall (A B : Type) (M : map A B),
  (forall x k, ~ binds M x k) -> M = \{}.
Proof using.
  intros A B M. simpl. unfold empty_impl, binds_impl.
  intros H. apply func_ext_1. intros x. cases (M x); auto_false*.
Qed.

Lemma dom_empty_inv : forall A B (M : map A B),
  dom M = \{} -> M = \{}.
Proof using.
  intros A B M. simpl. unfold dom_impl, empty_impl.
  intro H.
  admit.   (* todo: use lemma above and binds_dom *)
Qed.


End Properties.


Axiom restrict_read : forall A `{Inhab B} (M:map A B) i j,
  i <> j -> (M\--i)[j] = M[j].

Axiom restrict_update : forall A `{Inhab B} (M:map A B) i j v,
  i <> j -> (M\--i)[j:=v] = (M[j:=v] \--i).

Axiom dom_update_in : forall A i `{Inhab B} v (M:map A B),
  index M i -> dom (M[i:=v]) = dom M.

Lemma dom_update_in_variant:
  forall A `{Inhab B} (M M' : map A B) (D : set A) x v,
  M' = M[x:=v] ->
  D = dom M ->
  x \in D ->
  D = dom M'.
Proof using.
  intros. subst. rewrite dom_update_in; eauto.
Qed.

Axiom dom_restrict_in : forall A i j `{Inhab B} (M:map A B),
  index M j -> i <> j -> index (M\--i) j.

Axiom update_update_eq : forall A i `{Inhab B} v v' (M:map A B),
  M[i:=v][i:=v'] = M[i:=v'].

Implicit Arguments dom_update_in [A B [H]].
Implicit Arguments dom_restrict_in [A B [H]].



Lemma map_update_as_union : forall A B (M:map A B) x v,
  M[x:=v] = M \u (x \:= v).
Proof using. auto. Qed.

Axiom map_split : forall A (E:set A) B (M:map A B),
  M = (M \- E) \u (M \| E).
Axiom map_restrict_single : forall A (x:A) B `{Inhab B} (M:map A B),
  M \| \{x} = (x \:= (M[x])).
Lemma map_split_single : forall A (x:A) B `{Inhab B} (M:map A B),
  M = (M \- \{x}) \u (x \:= (M[x])).
Proof using. intros. rewrite~ <- map_restrict_single. apply map_split. Qed.



Axiom map_indom_update_inv : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  j \indom (m[i:=v]) -> (j = i \/ j \indom m).
Axiom map_indom_update_already : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  j \indom m -> j \indom (m[i:=v]).

(* TEMPORARY {Inhab B} not needed in the following axioms, I think *)
Axiom binds_def : forall A `{Inhab B} (M:map A B) x v,
  binds M x v = (x \indom M /\ M[x] = v).
Axiom binds_inv : forall A `{Inhab B} (M:map A B) x v,
  binds M x v -> (x \indom M /\ M[x] = v).
Axiom binds_prove : forall A `{Inhab B} (M:map A B) x v,
  x \indom M -> M[x] = v -> binds M x v.

Axiom binds_update_neq : forall A B i j v w (M:map A B),
  i <> j -> binds M i v -> binds (M[j:=w]) i v.

Axiom binds_update_eq : forall A B i v (M:map A B),
  binds (M[i:=v]) i v.

Axiom binds_update_neq_inv : forall A B i j v w (M:map A B),
  binds (M[j:=w]) i v -> i <> j -> binds M i v.
Axiom binds_update_neq_inv' : forall A B i j v w (M:map A B),
  binds (M[j:=w]) i v -> j \notin (dom M : set _) -> binds M i v.

Axiom binds_inj : forall A i `{Inhab B} v1 v2 (M:map A B),
  binds M i v1 -> binds M i v2 -> v1 = v2.

(*
Axiom binds_update_rem : forall A i j `{Inhab B} v w (M:map A B),
  j \notindom' M -> binds (M[j:=w]) i v -> binds M i v.
Hint Resolve binds_update_rem.
*)

Axiom binds_get : forall A `{Inhab B} (M:map A B) x v,
  binds M x v -> M[x] = v.
Axiom binds_dom : forall A `{Inhab B} (M:map A B) x v,
  binds M x v -> x \indom M.

Axiom dom_update_notin : forall A B i v (M:map A B),
  i \notin (dom M : set _) -> dom (M[i:=v]) = dom M \u \{i}.
  (* TEMPORARY semble vrai aussi sans l'hypothèse? *)

Axiom binds_index : forall A i `{Inhab B} v (M:map A B),
  binds M i v -> index M i.

Axiom binds_update_neq' : forall A i j `{Inhab B} v w (M:map A B),
  i <> j -> binds M i v -> binds (M[j:=w]) i v.

Axiom map_indom_update_already_inv : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  j \indom (m[i:=v]) -> i \indom m -> j \indom m.
Global Opaque binds_inst. 


Axiom map_update_read_if : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  (m[i:=v])[j] = If i = j then v else m[j].

Lemma binds_update_neq_iff: forall A `{Inhab B} i j v w (M:map A B),
  j \notin (dom M : set _) ->
  (binds M i v <-> binds (M[j:=w]) i v).
Proof using.
  split; intros.
  { eapply binds_update_neq; [ | eauto ].
    assert (i \indom M). { eapply binds_index; eauto. }
    intro. subst. unfold notin in *. tauto. }
  { eauto using binds_update_neq_inv'. }
Qed.

Lemma binds_update_analysis: forall A B i j v w (M:map A B),
  binds (M[j:=w]) i v ->
  i <> j /\ binds M i v \/
  i = j /\ v = w.
Proof using.
  intros.
  forwards [ ? ? ]: binds_inv.
Admitted.  (* COQBUG eexact H. *)

Lemma binds_update_indom_iff:
  forall A B (M : map A B) a1 a2 b1 b2,
  (a2 <> a1 /\ binds M a2 b2 \/ a2 = a1 /\ b2 = b1)
  <->
  binds (M[a1:=b1]) a2 b2.
Proof using.
  split. introv [ [ ? ? ] | [ ? ? ] ].
  { eauto using binds_update_neq. }
  { subst. eapply binds_update_eq. }
  { eauto using binds_update_analysis. }
Qed.

(* todo *)
Axiom map_indom_update : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  j \indom (m[i:=v]) = (j = i \/ j \indom m).
Lemma map_indom_update_self : forall A `{Inhab B} (m:map A B) (i:A) (v:B),
  i \indom (m[i:=v]).
Proof using. intros. rewrite~ map_indom_update. Qed.

Hint Resolve map_indom_update_self.

Axiom map_update_read_eq : forall A `{Inhab B} (m:map A B) (i:A) (v:B),
  (m[i:=v])[i] = v.
Axiom map_update_read_neq : forall A `{Inhab B} (m:map A B) (i j:A) (v:B),
  i<>j -> (m[i:=v])[j] = m[j].

Axiom map_update_restrict : forall A `{Inhab B} (m:map A B) (i:A) (v:B),
  (m[i:=v] \- \{i}) = (m \- \{i}).

Hint Rewrite @map_indom_update @map_update_read_neq @map_update_read_eq : rew_map.

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
(** ** Reduce on maps *)

(* TODO: rename to fold, use commutative monoids *)
(* used somewhere in CFML (?) *)
Require Import LibStruct.
Section Reduce.
Variables (A B C : Type).
Axiom reduce : (* UNDER CONSTRUCTION *)
  monoid_def C -> (A -> B -> C) -> map A B -> C.
Axiom reduce_empty : (* UNDER CONSTRUCTION *)
  forall m f, Monoid m ->
  reduce m f \{} = monoid_neutral m.
Axiom reduce_single : (* UNDER CONSTRUCTION *)
  forall x v m f, Monoid m ->
  reduce m f (x \:= v) = f x v.
Axiom reduce_union : (* UNDER CONSTRUCTION *)
  forall M1 M2 m f, Monoid m ->
  reduce m f (M1 \u M2) = (monoid_oper m) (reduce m f M1) (reduce m f M2).
End Reduce.


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
(** ** Properties *)

(* The following lemma is actually not used, because [discriminate] does the
   job. Perhaps this will fail someday if [binds] becomes opaque? *)

(* TODO use an instance *)

Goal
  forall A B a b,
  binds (\{} : map A B) a b ->
  False.
Proof using.
  intros. discriminate. (* ? *)
Qed.


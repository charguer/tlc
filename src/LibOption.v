(**************************************************************************
* TLC: A library for Coq                                                  *
* Option data-structure
**************************************************************************)

Set Implicit Arguments.
From TLC Require Import LibTactics LibReflect.
Generalizable Variables A.

(* --TODO: find a more explicit name? *)


(* ********************************************************************** *)
(** * Option type *)

(* ---------------------------------------------------------------------- *)
(** ** Definition *)

(** From the Prelude:

  Inductive option A : Type :=
    | Some : A -> option A
    | None : option A.

*)

Arguments Some {A}.
Arguments None {A}.


(* ---------------------------------------------------------------------- *)
(** ** Inhabited *)

#[global]
Instance Inhab_option : forall A, Inhab (option A).
Proof using. intros. apply (Inhab_of_val None). Qed.


(* ********************************************************************** *)
(** * Operations *)

(* ---------------------------------------------------------------------- *)
(** ** [is_some] *)

(** [is_some o] holds when [o] is of the form [Some x] *)

Definition is_some A (o:option A) :=
  match o with
  | None => false
  | Some _ => true
  end.


(* ---------------------------------------------------------------------- *)
(** ** [unsome_default] *)

(** [unsome_default d o] returns the content of the option, and returns [d]
    in case the option in [None]. *)

Definition unsome_default A d (o:option A) :=
  match o with
  | None => d
  | Some x => x
  end.


(* ---------------------------------------------------------------------- *)
(** ** [unsome] *)

(** [unsome o] returns the content of the option, and returns an arbitrary
    value in case the option in [None]. *)

Definition unsome `{Inhab A} :=
  unsome_default (arbitrary (A:=A)).


(* ---------------------------------------------------------------------- *)
(** ** [map] *)

(** [map f o] takes an option and returns an option, and maps the function
    [f] to the content of the option if it has one. *)

Definition map A B (f : A -> B) (o : option A) : option B :=
  match o with
  | None => None
  | Some x => Some (f x)
  end.

Lemma map_eq_none_inv : forall A B (f : A->B) o,
  map f o = None ->
  o = None.
Proof using. introv H. destruct o; simpl; inverts* H. Qed.

Lemma map_eq_some_inv : forall A B (f : A->B) o x,
  map f o = Some x ->
  exists z, o = Some z /\ x = f z.
Proof using. introv H. destruct o; simpl; inverts* H. Qed.

Arguments map_eq_none_inv [A] [B] [f] [o].
Arguments map_eq_some_inv [A] [B] [f] [o] [x].


(* ---------------------------------------------------------------------- *)
(** ** [map_on] *)

(* --TODO: is this really useful? *)
(** [map_on o f] is the same as [map f o], only the arguments are swapped. *)

Definition map_on A B (o : option A) (f : A -> B) : option B :=
  map f o.

Lemma map_on_eq_none_inv : forall A B (f : A -> B) o,
  map f o = None ->
  o = None.
Proof using. introv H. destruct~ o; tryfalse. Qed.

Lemma map_on_eq_some_inv : forall A B (f : A -> B) o x,
  map_on o f = Some x ->
  exists z, o = Some z /\ x = f z.
Proof using. introv H. destruct o; simpl; inverts* H. Qed.

Arguments map_eq_none_inv [A] [B] [f] [o].
Arguments map_on_eq_some_inv [A] [B] [f] [o] [x].


(* ---------------------------------------------------------------------- *)
(** ** [apply] *)

(** [apply f o] optionnaly applies a function of type [A -> option B] *)

Definition apply A B (f : A->option B) (o : option A) : option B :=
  match o with
  | None => None
  | Some x => f x
  end.


(* ---------------------------------------------------------------------- *)
(** ** [apply_on] *)

(* --TODO: is this really useful? *)
(** [apply_on o f] is the same as [apply f o] *)

Definition apply_on A B (o : option A) (f : A->option B) : option B:=
  apply f o.

Lemma apply_on_eq_none_inv : forall A B (f : A->option B) o,
  apply_on o f = None ->
     (o = None)
  \/ (exists x, o = Some x /\ f x = None).
Proof using. introv H. destruct o; simpl; inverts* H. Qed.

Lemma apply_on_eq_some_inv : forall A B (f : A->option B) o x,
  apply_on o f = Some x ->
  exists z, o = Some z /\ f z = Some x.
Proof using. introv H. destruct o; simpl; inverts* H. Qed.

Arguments apply_on_eq_none_inv [A] [B] [f] [o].
Arguments apply_on_eq_some_inv [A] [B] [f] [o] [x].





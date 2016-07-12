

Ltac invert_one_step :=
  match goal with | H : ?T |- _ =>  
  match type of T with Prop =>
     inversion H; subst
  end end.

Ltac invert_one :=
     solve [ invert_one_step ] 
  || fail "The goal is not solvable by inversion of an hypothesis.".

(* Replacement for "solve by inversion":
   "invert_one". *)

(* Replacement for "try solve by inversion":
   "try invert_one". *)

(* Replacement for "solve by inversion 2":
   "try solve [ invert_one; invert_one ]". *)

Lemma invert_one_demo_1 : forall (n:nat), True.
Proof using. intros. try invert_one. Abort.

Lemma invert_one_demo_2 : forall (n:nat), False -> False.
Proof using. intros. invert_one. Qed.
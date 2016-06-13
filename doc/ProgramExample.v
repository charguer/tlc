Require Import Program ZArith.
Require Import LibTactics.

Program Fixpoint f (n : nat) { measure n } : nat :=
  match n with 
  | 0 => 0 
  | 1 => 1
  | _ => f (n-1) + f (n-2)
  end.
Next Obligation.
omega.
Qed.
Next Obligation.
omega.
Qed.

Lemma f_fix : forall n, 
  f n =
  match n with 
  | 0 => 0 
  | 1 => 1
  | _ => f (n-1) + f (n-2)
  end.
Proof.
  intros.
  unfold f at 1.
  rewrite WfExtensionality.fix_sub_eq_ext.
  fold f.
  fold f.
  destruct n. auto. destruct n. auto. auto.
Qed.


Lemma test_calcul1 : f 1 = 1.
Proof. reflexivity. Qed.
Lemma test_calcul2 : f 2 = 1.
Proof. reflexivity. Qed.
Lemma test_calcul3 : f 3 = 2.
Proof. reflexivity. Qed.

Lemma test : forall n, n >= 3 -> 
  f n = 2 * f (n-2) + f (n-3).
Proof.
  intros n. pattern n. apply (well_founded_ind lt_wf).
  clear n. intros n IH Hn.
  rewrite f_fix.
Admitted.



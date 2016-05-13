
diff --git a/src/LibEnv.v b/src/LibEnv.v
index 52f35cd..a1eca94 100644
--- a/src/LibEnv.v
+++ b/src/LibEnv.v
@@ -986,6 +986,44 @@ Proof using.
   introv F. applys~ binds_concat_left. applys binds_tail.
 Qed.
 
+Lemma double_binds_false: forall E1 E2 x v v',
+  ok (E1 & x ~ v & E2 & x ~ v') -> False.
+Proof.
+  intros.
+  apply ok_push_inv in H. destruct H as [H Hnot].
+  assert (binds x v (E1 & x ~ v & E2)) as HBi. {
+    lets Ht: (binds_tail x v E1).
+    apply (binds_concat_left_ok H Ht).
+  }
+  false (binds_fresh_inv HBi Hnot).
+Qed.
+
+Lemma binds_middle: forall E1 E2 E1' E2' x v v',
+  ok (E1 & x ~ v & E2) ->
+  E1 & x ~ v & E2 = E1' & x ~ v' & E2' ->
+  E1 = E1' /\ v = v' /\ E2 = E2'.
+Proof.
+  introv Hok. gen E1' E2'. induction E2 using env_ind; intros.
+  - rewrite concat_empty_r in H.
+    destruct E2' using env_ind.
+    + rewrite concat_empty_r in H. apply eq_push_inv in H.
+      destruct H as [_ [Hv Hs]]. auto.
+    + rewrite concat_assoc in H. rewrite concat_empty_r in Hok.
+      lets Heq: (eq_push_inv H).
+      destruct Heq as [Hx [Hv Hs]]. subst.
+      false (double_binds_false Hok).
+  - destruct E2' using env_ind.
+    + rewrite concat_empty_r in H. rewrite concat_assoc in H. apply eq_push_inv in H.
+      destruct H as [Hx [Hv Hs]]. subst.
+      rewrite concat_assoc in Hok.
+      false (double_binds_false Hok).
+    + repeat rewrite concat_assoc in H.
+      apply eq_push_inv in H. destruct H as [Hx [Hv Hs]]. subst.
+      rewrite concat_assoc in Hok. apply ok_push_inv_ok in Hok.
+      specialize (IHE2 Hok E1' E2' Hs).
+      destruct IHE2 as [Hs' [Hv Hs'']]. subst. auto.
+Qed.
+
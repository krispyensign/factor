Add LoadPath "./proofs/" as proofs.
Load W.

Theorem ZWf_eq : forall (f : Z->Z) (v w : Z),
  (v = 0 /\ w = (f 0)) \/
  (v = 1 /\ w = (f 1)) \/
  (v = 2 /\ w = (f 2)) \/
  (v = 3 /\ w = (f 3)) ->
  (Wf f v) = w.
Proof.
  intros.
  unfold Wf. unfold W. unfold k. unfold j. unfold i.
  destruct H as [H0 | [H1 | [H2 | H3]]].
  - destruct H0. subst. simpl. lia.
  - destruct H1. subst. simpl. lia.
  - destruct H2. subst. simpl. lia.
  - destruct H3. subst. simpl. lia.
Qed.

(*
  For any periodic function f, Wf f is also periodic
*)
Theorem ZWf_mod_add_l : forall (f : Z->Z) (u v : Z),
  (Wf f (4*u + v)) = (Wf f v).
Proof.
  intros.
  unfold Wf. unfold W.
  rewrite Zj_mod_add.
  rewrite Zk_mod_add.
  rewrite Zi_mod_add_4.
  reflexivity.
Qed.

(*
  Deconvolutes f(t, v) => a + b*f(t)*i(v) + c*f(t)*j(v) + d*f(t)*k(v)
  when f(t,v) is periodic when t or v is held constant.
*)
Theorem ZWff_mod_add_l : forall (f : Z->Z->Z) (t u v : Z),
  (Wf (f t) (4*u + v)) = (Wf (f t) v).
Proof.
  intros.
  unfold Wf. unfold W.
  rewrite Zj_mod_add.
  rewrite Zk_mod_add.
  rewrite Zi_mod_add_4.
  reflexivity.
Qed.

(*
  Proves that repeated application eliminates other applications
*)
Theorem ZWf_Wf_l : forall (f : Z->Z) (u v : Z),
  0 <= v < 4 ->
  (Wf (Wf f) (4*u + v)) = (Wf f v).
Proof.
  intros.
  unfold Wf. rewrite ZW_W_l.
  reflexivity.
  assumption.
Qed.

(*
  Proves that repeated application eliminates other applications
*)
Theorem ZWf_Wff_l : forall (f : Z->Z->Z) (t u v : Z),
  0 <= v < 4 ->
  (Wf (Wf (f t)) (4*u + v)) = (Wf (f t) v).
Proof.
  intros.
  unfold Wf. rewrite ZW_W_l.
  reflexivity.
  assumption.
Qed.

Theorem ZWf_Wf_add_l : forall (g f : Z->Z) (u v : Z),
  0 <= v < 4 ->
  (Wf (zip g (Wf f)) (4*u + v)) = (Wf (zip g f) v).
Proof.
  intros.
  unfold zip. unfold Wf. 
  replace (W (f 0) (f 1) (f 2) (f 3) 0) with (f 0).
  replace (W (f 0) (f 1) (f 2) (f 3) 1) with (f 1).
  replace (W (f 0) (f 1) (f 2) (f 3) 2) with (f 2).
  replace (W (f 0) (f 1) (f 2) (f 3) 3) with (f 3).
  rewrite ZW_mod_add_l.
  - reflexivity.
  - assumption.
  - symmetry. rewrite ZW_eq with (w := (f 3)). reflexivity. auto.
  - symmetry. rewrite ZW_eq with (w := (f 2)). reflexivity. auto.
  - symmetry. rewrite ZW_eq with (w := (f 1)). reflexivity. auto.
  - symmetry. rewrite ZW_eq with (w := (f 0)). reflexivity. auto.
Qed.


Theorem ZWf_Wff_add_l : forall (g f : Z->Z->Z) (t u v : Z),
  0 <= v < 4 ->
  (Wf (zip (g t) (Wf (f t))) (4*u + v)) = (Wf (zip (g t) (f t)) v).
Proof.
  intros.
  unfold zip. unfold Wf.
  replace (W (f t 0) (f t 1) (f t 2) (f t 3) 0) with (f t 0).
  replace (W (f t 0) (f t 1) (f t 2) (f t 3) 1) with (f t 1).
  replace (W (f t 0) (f t 1) (f t 2) (f t 3) 2) with (f t 2).
  replace (W (f t 0) (f t 1) (f t 2) (f t 3) 3) with (f t 3).
  rewrite ZW_mod_add_l.
  - reflexivity.
  - assumption.
  - symmetry. rewrite ZW_eq with (w := (f t 3)). reflexivity. auto.
  - symmetry. rewrite ZW_eq with (w := (f t 2)). reflexivity. auto.
  - symmetry. rewrite ZW_eq with (w := (f t 1)). reflexivity. auto.
  - symmetry. rewrite ZW_eq with (w := (f t 0)). reflexivity. auto.
Qed.


Theorem ZWf_if_l : forall (u v : Z),
  0 <= v < 4 ->
  (Wf i (4*u + v)) = (i v).
Proof.
  intros.
  rewrite ZWf_mod_add_l.
  unfold Wf.
  rewrite ZW_eq with (w := (i v)).
  - reflexivity.
  - unfold i. lia.
Qed.

Theorem ZWf_jf_l : forall (u v : Z),
  0 <= v < 4 ->
  (Wf j (4*u + v)) = (j v).
Proof.
  intros.
  rewrite ZWf_mod_add_l.
  unfold Wf.
  rewrite ZW_eq with (w := (j v)).
  - reflexivity.
  - unfold j. unfold i. lia.
Qed.

Theorem ZWf_kf_l : forall (u v : Z),
  0 <= v < 4 ->
  (Wf k (4*u + v)) = (k v).
Proof.
  intros.
  rewrite ZWf_mod_add_l.
  unfold Wf.
  rewrite ZW_eq with (w := (k v)).
  - reflexivity.
  - unfold k. unfold j. unfold i. lia.
Qed.
Require Import BinInt.
Require Import ZArith.
Require Import Lia.

Local Open Scope Z_scope.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.


Definition i n := 1 - 2*(n mod 2).
Definition j n := - (n mod 4) + (1 - (i n))/2 + 1.
Definition k n := (j (n + 1)).
Definition W a b c d n :=
  ((a + b + c + d) +
  (a - b + c - d)*(i n) +
  (a + b - c - d)*(j n) +
  (a - b - c + d)*(k n))/4.
Definition Wf (f : Z->Z) (n : Z) := (W (f 0) (f 1) (f 2) (f 3) n).
Definition zip (f g : Z->Z) (n : Z) := (f n) + (g n).


Lemma Zmod_add_r : forall a b c, c <> 0 -> (c * b + a) mod c = a mod c.
Proof.
  intros.
  rewrite Z.mul_comm.
  rewrite Z.add_comm.
  rewrite Z.mod_add.
  reflexivity.
  assumption.
Qed.


Lemma Zmod_mul_add : forall a b c d, c <> 0 -> (c * b * d + a) mod c = a mod c.
Proof.
  intros.
  pose (k := b * d).
  replace (c*b*d) with (c*k).
  rewrite Zmod_add_r.
  - reflexivity.
  - assumption.
  - subst k. rewrite Z.mul_assoc. reflexivity.
Qed.


Theorem Zi_mod_add : forall x k, (i (2*k + x)) = (i x).
Proof.
  intros.
  unfold i.
  rewrite Zmod_add_r.
  reflexivity.
  discriminate.
Qed.


Theorem Zi_mod_add_4 : forall a b, (i (4*a + b)) = (i b).
Proof.
  intros.
  unfold i.
  replace (4*a) with (2*(2*a)).
  rewrite Zmod_add_r.
  reflexivity.
  discriminate.
  lia.
Qed.


Theorem Zi_eq : forall a b c, 
  (b = 0 /\ c = 1) \/ (b = 1 /\ c = -1) ->
  (i (2*a + b)) = c.
Proof.
  intros.
  destruct H as [(b0, c0) | (b1, c1)].
  - subst. rewrite Zi_mod_add. auto.
  - subst. rewrite Zi_mod_add. auto.
Qed.


Theorem Zi_pow_2_r : forall a b, b = 0 \/ b = 1 -> (i (2*a + b)) ^ 2 = 1.
Proof.
  intros.
  destruct H.
  - subst. rewrite Zi_mod_add. auto.
  - subst. rewrite Zi_mod_add. auto.
Qed.


Theorem Zj_mod_add : forall a b, (j (4*a + b)) = (j b).
Proof.
  intros.
  unfold j.
  rewrite Zmod_add_r.
  unfold i.
  replace (4) with (2 * 2).
  rewrite Zmod_mul_add.
  - reflexivity.
  - discriminate.
  - simpl. reflexivity.
  - discriminate.
Qed.


Theorem Zj_eq : forall a b c,
  (b = 0 /\ c = 1) \/
  (b = 1 /\ c = 1) \/
  (b = 2 /\ c = -1) \/
  (b = 3 /\ c = -1) ->
  (j (4*a + b)) = c.
Proof.
  intros.
  rewrite Zj_mod_add.
  destruct H as [(b0, c0) | [(b1, c1) | [(b2, c2) | (b3, c3)]]].
  - subst. auto.
  - subst. auto.
  - subst. auto.
  - subst. auto.
Qed.


Theorem Zj_pow_2_r : forall a b,
  b = 0 \/ b = 1 \/ b = 2 \/ b = 3 ->
  (j (4*a + b))^2 = 1.
Proof.
  intros.
  rewrite Zj_mod_add.
  destruct H as [b0 | [b1 | [b2 | b3]]].
  - subst. auto.
  - subst. auto.
  - subst. auto.
  - subst. auto.
Qed.


Theorem Zj_mul_2_l : forall a, (j (2*a)) = (i a).
Proof.
  intros.
  unfold j.
  rewrite Z.mul_comm with (m := a) (n := 2).
  unfold i.
  rewrite Z.mod_mul.
  zify.
  lia.
  discriminate.
Qed.


Theorem Zk_mod_add : forall a b, (k (4*a + b)) = (k b).
Proof.
  intros.
  unfold k.
  rewrite <- Z.add_assoc.
  rewrite Zj_mod_add.
  auto.
Qed.


Theorem Zk_eq : forall a b c,
  (b = 0 /\ c = 1) \/
  (b = 1 /\ c = -1) \/
  (b = 2 /\ c = -1) \/
  (b = 3 /\ c = 1) ->
  (k (4*a + b)) = c.
Proof.
  intros.
  rewrite Zk_mod_add.
  destruct H as [(b0, c0) | [(b1, c1) | [(b2, c2) | (b3, c3)]]].
  - subst. auto.
  - subst. auto.
  - subst. auto.
  - subst. auto.
Qed.


Theorem Zk_pow_2_r : forall a b,
  b = 0 \/ b = 1 \/ b = 2 \/ b = 3 ->
  (k (4*a + b))^2 = 1.
Proof.
  intros.
  rewrite Zk_mod_add.
  destruct H as [b0 | [b1 | [b2 | b3]]].
  - subst. auto.
  - subst. auto.
  - subst. auto.
  - subst. auto.
Qed.


Theorem Zi_add_1_l : forall a, a = 0 \/ a = 1 -> (i (a + 1)) = -(i a).
Proof.
  intros.
  destruct H.
  - subst. auto.
  - subst. auto.
Qed.


Theorem Zj_mul_add_1_l : forall a, (j (2*a + 1)) = (i a).
Proof.
  intros.
  unfold j.
  rewrite Zi_mod_add.
  unfold i.
  lia.
Qed.


Theorem Zk_mul_2_l : forall a, (k (2*a)) = (i a).
Proof.
  intros.
  unfold k.
  rewrite Zj_mul_add_1_l.
  reflexivity.
Qed.


Theorem ZW_eq : forall a b c d v w,
  (v = 0 /\ w = a) \/
  (v = 1 /\ w = b) \/
  (v = 2 /\ w = c) \/
  (v = 3 /\ w = d) ->
  (W a b c d v) = w.
Proof.
  intros.
  unfold W. unfold k. unfold j. unfold i.
  destruct H as [H0 | [H1 | [H2 | H3]]].
  - destruct H0. subst. simpl. lia.
  - destruct H1. subst. simpl. lia.
  - destruct H2. subst. simpl. lia.
  - destruct H3. subst. simpl. lia.
Qed.


Theorem ZW_mod_add_l : forall a b c d u v,
  v = 0 \/ v = 1 \/ v = 2 \/ v = 3 ->
  (W a b c d (4*u + v)) = (W a b c d v).
Proof.
  intros.
  unfold W.
  rewrite Zj_mod_add.
  rewrite Zk_mod_add.
  rewrite Zi_mod_add_4.
  reflexivity.
Qed.


Theorem ZW_W_l : forall a b c d u v,
  v = 0 \/ v = 1 \/ v = 2 \/ v = 3 ->
  (W (W a b c d 0)
    (W a b c d 1)
    (W a b c d 2)
    (W a b c d 3)
    (4*u + v)) = (W a b c d v).
Proof.
  intros.
  rewrite ZW_mod_add_l.
  unfold W. unfold W. unfold k. unfold j. unfold i.
  destruct H as [H0 | [H1 | [H2 | H3]]].
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - assumption.
Qed.


Theorem ZW_W_add_l : forall a b c d e f g h u v,
  v = 0 \/ v = 1 \/ v = 2 \/ v = 3 ->
  (W  ((W a b c d 0) + e)
    ((W a b c d 1) + f)
    ((W a b c d 2) + g)
    ((W a b c d 3) + h)
    (4*u + v)) = (W (a + e) (b + f) (c + g) (d + h) v).
Proof.
  intros.
  rewrite ZW_mod_add_l.
  unfold W. unfold W. unfold k. unfold j. unfold i.
  destruct H as [H0 | [H1 | [H2 | H3]]].
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - assumption.
Qed.


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
  v = 0 \/ v = 1 \/ v = 2 \/ v = 3 ->
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
  v = 0 \/ v = 1 \/ v = 2 \/ v = 3 ->
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
  v = 0 \/ v = 1 \/ v = 2 \/ v = 3 ->
  (Wf (Wf f) (4*u + v)) = (Wf f v).
Proof.
  intros.
  rewrite ZWf_mod_add_l.
  unfold Wf. repeat unfold W. unfold k. unfold j. unfold i.
  destruct H as [H0 | [H1 | [H2 | H3]]].
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - assumption.
Qed.

(*
  Proves that repeated application eliminates other applications
*)
Theorem ZWf_Wff_l : forall (f : Z->Z->Z) (t u v : Z),
  v = 0 \/ v = 1 \/ v = 2 \/ v = 3 ->
  (Wf (Wf (f t)) (4*u + v)) = (Wf (f t) v).
Proof.
  intros.
  rewrite ZWf_mod_add_l.
  unfold Wf. repeat unfold W. unfold k. unfold j. unfold i.
  destruct H as [H0 | [H1 | [H2 | H3]]].
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - assumption.
Qed.

Theorem ZWf_Wf_add_l : forall (g f : Z->Z) (u v : Z),
  v = 0 \/ v = 1 \/ v = 2 \/ v = 3 ->
  (Wf (zip g (Wf f)) (4*u + v)) = (Wf (zip g f) v).
Proof.
  intros.
  rewrite ZWf_mod_add_l.
  unfold zip. unfold Wf. repeat unfold W. unfold k. unfold j. unfold i.
  destruct H as [H0 | [H1 | [H2 | H3]]].
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - assumption.
Qed.

Theorem ZWf_Wff_add_l : forall (g f : Z->Z->Z) (t u v : Z),
  v = 0 \/ v = 1 \/ v = 2 \/ v = 3 ->
  (Wf (zip (g t) (Wf (f t))) (4*u + v)) = (Wf (zip (g t) (f t)) v).
Proof.
  intros.
  rewrite ZWf_mod_add_l.
  unfold zip. unfold Wf. repeat unfold W. unfold k. unfold j. unfold i.
  destruct H as [H0 | [H1 | [H2 | H3]]].
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - assumption.
Qed.


Theorem ZWf_if_l : forall (u v : Z),
  v = 0 \/ v = 1 \/ v = 2 \/ v = 3 ->
  (Wf i (4*u + v)) = (i v).
Proof.
  intros.
  rewrite ZWf_mod_add_l.
  unfold Wf. unfold W. unfold k. unfold j. unfold i.
  destruct H as [H0 | [H1 | [H2 | H3]]].
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - assumption.
Qed.

Theorem ZWf_jf_l : forall (u v : Z),
  v = 0 \/ v = 1 \/ v = 2 \/ v = 3 ->
  (Wf j (4*u + v)) = (j v).
Proof.
  intros.
  rewrite ZWf_mod_add_l.
  unfold Wf. unfold W. unfold k. unfold j. unfold i.
  destruct H as [H0 | [H1 | [H2 | H3]]].
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - assumption.
Qed.

Theorem ZWf_kf_l : forall (u v : Z),
  v = 0 \/ v = 1 \/ v = 2 \/ v = 3 ->
  (Wf k (4*u + v)) = (k v).
Proof.
  intros.
  rewrite ZWf_mod_add_l.
  unfold Wf. unfold W. unfold k. unfold j. unfold i.
  destruct H as [H0 | [H1 | [H2 | H3]]].
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - subst. simpl. lia.
  - assumption.
Qed.

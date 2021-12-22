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
  (b = 0 /\ c = 1) \/ (b = 1 /\ c = (-1)) ->
  (i (2*a + b)) = c.
Proof.
  intros.
  destruct H as [(b0, c0) | (b1, c1)].
  - subst. rewrite Zi_mod_add. auto.
  - subst. rewrite Zi_mod_add. auto.
Qed.


Theorem Zi_pow_2_r : forall a b, 0 <= b < 2 -> (i (2*a + b)) ^ 2 = 1.
Proof.
  intros.
  rewrite Zi_mod_add.
  unfold i.
  nia.
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
  0 <= b < 4 ->
  (j (4*a + b))^2 = 1.
Proof.
  intros.
  rewrite Zj_mod_add.
  unfold j.
  unfold i.
  nia.
Qed.


Theorem Zj_mul_2_l : forall a, (j (2*a)) = (i a).
Proof.
  intros.
  unfold j.
  rewrite Z.mul_comm with (m := a) (n := 2).
  unfold i.
  rewrite Z.mod_mul.
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
  0 <= b < 4 ->
  (k (4*a + b))^2 = 1.
Proof.
  intros.
  rewrite Zk_mod_add.
  unfold k. unfold j. unfold i.
  nia.
Qed.


Theorem Zi_add_1_l : forall a, a = 0 \/ a = 1 -> (i (a + 1)) = (-(i a)).
Proof.
  intros.
  destruct H.
  - subst. auto.
  - subst. auto.
Qed.


Theorem Zi_add_l : forall a b, (i (a + b)) = (i a)*(i b).
Proof.
  intros.
  unfold i.
  nia.
Qed.


Theorem Zi_sub_l : forall a b, (i (a - b)) = (i a)*(i b).
Proof.
  intros.
  unfold i.
  nia.
Qed.

Theorem Zi_i_l : forall a,
  (i (i a)) = (-1).
Proof.
  intros.
  unfold i.
  lia.
Qed.


Theorem Zi_expr_1 : forall a, (i (2*a + ((i a)/2) + 1/2)) = (i (a + 1)).
Proof.
  intros.
  rewrite <- Z.add_assoc.
  rewrite Zi_eq with (c := (i (a + 1))).
  reflexivity.
  left.
  split.
  replace a with 1.
  unfold i.
  rewrite Z.mod_small.
  rewrite Z.mul_1_r.
  replace (1 - 2) with (-1).
  replace ((-1)/2 + 1/2) with ((-1 + 1)/2).
  lia.
  unfold i.
  replace (((1 - 2 * (a mod 2)) / 2 + 1 / 2)) with (1 - 2 * (a mod 2)).
  rewrite Z.mod_mod.
Qed.

Theorem Zi_expr_2 : forall a b, (i (a - (i b) + 1)) = (i a).
Proof.
  intros.
  unfold i.
  lia.
Qed.

Theorem Zi_expr_3 : forall a, (i ((2*a - (i a)/2 + 1/2))) = (i a).
Proof.
  intros.
  unfold i.
  lia.
Qed.


Theorem Zi_expr_4 : forall a b, (i (a + (i b)/2 + 1/2)) = (i a)*(i (b + 1)).
Proof.
  intros.
  unfold i.
  lia.
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
  0 <= v < 4 ->
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
  0 <= v < 4 ->
  (W (W a b c d 0)
    (W a b c d 1)
    (W a b c d 2)
    (W a b c d 3)
    (4*u + v)) = (W a b c d v).
Proof.
  intros.
  rewrite ZW_mod_add_l.
  replace (W a b c d 0) with a.
  replace (W a b c d 1) with b.
  replace (W a b c d 2) with c.
  replace (W a b c d 3) with d.
  - reflexivity.
  - symmetry. rewrite ZW_eq with (w := d). reflexivity. auto.
  - symmetry. rewrite ZW_eq with (w := c). reflexivity. auto.
  - symmetry. rewrite ZW_eq with (w := b). reflexivity. auto.
  - symmetry. rewrite ZW_eq with (w := a). reflexivity. auto.
  - assumption.
Qed.


Theorem ZW_W_add_l : forall a b c d e f g h u v,
  0 <= v < 4 ->
  (W  ((W a b c d 0) + e)
    ((W a b c d 1) + f)
    ((W a b c d 2) + g)
    ((W a b c d 3) + h)
    (4*u + v)) = (W (a + e) (b + f) (c + g) (d + h) v).
Proof.
  intros.
  rewrite ZW_mod_add_l.
  replace (W a b c d 0) with a.
  replace (W a b c d 1) with b.
  replace (W a b c d 2) with c.
  replace (W a b c d 3) with d.
  - reflexivity.
  - symmetry. rewrite ZW_eq with (w := d). reflexivity. auto.
  - symmetry. rewrite ZW_eq with (w := c). reflexivity. auto.
  - symmetry. rewrite ZW_eq with (w := b). reflexivity. auto.
  - symmetry. rewrite ZW_eq with (w := a). reflexivity. auto.
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


Theorem Zj_add_l : forall a b,
  0 <= a < 4 ->
  0 <= b < 4 ->
(j (a + b)) = (W (j a) (k a) (-(j a)) (-(k a)) b).
Proof.
  intros.
  symmetry.
  rewrite ZW_eq with (w := (j (a + b))).
  - reflexivity.
  - unfold k. unfold j. unfold i. lia.
Qed.


Theorem Zk_add_l : forall a b,
  0 <= a < 4 ->
  0 <= b < 4 ->
  (k (a + b)) = (W (k a) (-(j a)) (-(k a)) (j a) b).
Proof.
  intros.
  symmetry.
  rewrite ZW_eq with (w := (k (a + b))).
  - reflexivity.
  - unfold k. unfold j. unfold i. lia.
Qed.
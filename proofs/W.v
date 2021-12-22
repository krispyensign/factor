Add LoadPath "./proofs/" as proofs.
Load w3.

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
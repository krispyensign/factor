Add LoadPath "./proofs/" as proofs.
Load w2.

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
  unfold k.
  unfold j.
  unfold i.
  nia.
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


Theorem Zk_mul_2_l : forall a, (k (2*a)) = (i a).
Proof.
  intros.
  unfold k.
  rewrite Zj_mul_add_1_l.
  reflexivity.
Qed.

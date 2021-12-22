Add LoadPath "./proofs/" as proofs.
Load w1.

Theorem Zj_mod_add : forall a b, (j (4*a + b)) = (j b).
Proof.
  intros.
  unfold j.
  rewrite Zmod_add_r.
  unfold i.
  lia.
  discriminate.
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
  unfold j.
  unfold i.
  lia.
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

Theorem Zj_mul_add_1_l : forall a, (j (2*a + 1)) = (i a).
Proof.
  intros.
  unfold j.
  rewrite Zi_mod_add.
  unfold i.
  lia.
Qed.

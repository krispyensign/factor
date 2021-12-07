Require Import BinInt.
Require Import BinNat.
Require Import Zpow_facts.

Local Open Scope Z_scope.

Definition i x := 1 - 2*(x mod 2).
Definition j x := - (x mod 4) + (x mod 2) + 1.
Definition k x := j(x + 1).

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

Theorem Zi_mod_add : forall x k, i(2*k + x) = i(x).
Proof.
	unfold i.
	intros.
	rewrite Zmod_add_r.
	reflexivity.
	discriminate.
Qed.

Theorem Zi_eq : forall a b c,
	(b = 0 /\ c = 1) \/ (b = 1 /\ c = -1) ->
	i(2*a + b) = c.
Proof.
	intros a b c [H0 | H1].
	- destruct H0 as [b0 c0]. rewrite Zi_mod_add. subst. auto.
	- destruct H1 as [b1 c1]. rewrite Zi_mod_add. subst. auto.
Qed.

Theorem Zi_pow_2_r : forall a b,
  b = 0 \/ b = 1 ->
	i (2*a + b) ^ 2 = 1.
Proof.
	intros a b [b0 | b1].
	- subst. rewrite Zi_mod_add. auto.
	- subst. rewrite Zi_mod_add. auto.
Qed.

Theorem Zj_mod_add : forall x k, j(4*k + x) = j(x).
Proof.
	intros.
	unfold j.
	rewrite Zmod_add_r.
	replace (4) with (2 * 2).
	rewrite Zmod_mul_add.
	- reflexivity.
	- discriminate.
	- simpl. reflexivity.
	- discriminate.
Qed.

Theorem Zj_eq : forall a b c,
	(b = 0 /\ c = 1) \/ (b = 1 /\ c = 1) \/ (b = 2 /\ c = -1) \/ (b = 3 /\ c = -1) ->
	j(4*a + b) = c.
Proof.
	intros a b c HN.
	rewrite Zj_mod_add.
	destruct HN as [(b0, c0) | HN]. subst. auto.
	- destruct HN as [(b1, c1) | HN]. subst. auto.
		* destruct HN as [(b2, c2) | (b3, c3)]. subst. auto.
			+ subst. auto.
Qed.

Theorem Zj_pow_2_r : forall a b,
	b = 0 \/
	b = 1 \/
	b = 2 \/
	b = 3 ->
	j(4*a + b)^2 = 1.
Proof.
	intros.
	rewrite Zj_mod_add.
	destruct H as [H0 | HN]. subst. auto.
	- destruct HN as [H1 | HN]. subst. auto.
		* destruct HN as [H2 | H3]. subst. auto.
			+ subst. auto.
Qed.

Theorem Zj_mul_2_l : forall a,
	j(2*a) = i(a).
Proof.
	intros.
	unfold j.
	rewrite Z.mul_comm with (m := a) (n := 2).
	rewrite Z.mod_mul.
	rewrite Z.add_0_r.
	rewrite Z.add_comm.
	rewrite Z.add_opp_r.
	unfold i.
	replace 4 with (2*2).
	rewrite Z.mul_mod_distr_r.
	rewrite Z.mul_comm.
	reflexivity.
	discriminate.
	discriminate.
	simpl. auto.
	discriminate.
Qed.

Theorem Zk_mod_add : forall a b, 
	k(4*a + b) = k(b).
Proof.
	intros.
	unfold k.
	rewrite <- Z.add_assoc.
	rewrite Zj_mod_add.
	auto.
Qed.

Theorem Zk_eq : forall a b c,
	(b = 0 /\ c = 1) \/ (b = 1 /\ c = -1) \/ (b = 2 /\ c = -1) \/ (b = 3 /\ c = 1) ->
	k(4*a + b) = c.
Proof.
	intros a b c HN.
	rewrite Zk_mod_add.
	destruct HN as [(b0, c0) | HN]. subst. auto.
	- destruct HN as [(b1, c1) | HN]. subst. auto.
		* destruct HN as [(b2, c2) | (b3, c3)]. subst. auto.
			+ subst. auto.
Qed.

Theorem Zk_pow_2_r : forall a b,
	b = 0 \/
	b = 1 \/
	b = 2 \/
	b = 3 ->
	k(4*a + b)^2 = 1.
Proof.
	intros.
	rewrite Zk_mod_add.
	destruct H as [H0 | HN]. subst. auto.
	- destruct HN as [H1 | HN]. subst. auto.
		* destruct HN as [H2 | H3]. subst. auto.
			+ subst. auto.
Qed.


Require Import BinInt.
Require Import ZArith.
Require Import Lia.

Local Open Scope Z_scope.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.


Definition i x := 1 - 2*(x mod 2).
Definition j x := - (x mod 4) + (1 - i(x))/2 + 1.
Definition k x := j(x + 1).
Definition H (a : Z) (b : Z) (c : Z) (d : Z) (x : Z) :=
	((a + b + c + d) +
	(a - b + c - d)*i(x) +
	(a + b - c - d)*j(x) +
	(a - b - c + d)*k(x))/4.


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
	intros.
	unfold i.
	rewrite Zmod_add_r.
	reflexivity.
	discriminate.
Qed.


Theorem Zi_eq : forall a b c, (b = 0 /\ c = 1) \/ (b = 1 /\ c = -1) ->
	i(2*a + b) = c.
Proof.
	intros.
	destruct H as [[b0 c0] | [b1 c1]].
	- subst. rewrite Zi_mod_add. auto.
	- subst. rewrite Zi_mod_add. auto.
Qed.


Theorem Zi_pow_2_r : forall a b, b = 0 \/ b = 1 -> i (2*a + b) ^ 2 = 1.
Proof.
	intros a b [b0 | b1].
	- subst. rewrite Zi_mod_add. auto.
	- subst. rewrite Zi_mod_add. auto.
Qed.


Theorem Zj_mod_add : forall a b, j(4*a + b) = j(b).
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
	(b = 0 /\ c = 1) \/ (b = 1 /\ c = 1) \/ (b = 2 /\ c = -1) \/ (b = 3 /\ c = -1) ->
	j(4*a + b) = c.
Proof.
	intros.
	rewrite Zj_mod_add.
	destruct H as [(b0, c0) | [(b1, c1) | [(b2, c2) | (b3, c3)]]].
	- subst. auto.
	- subst. auto.
	- subst. auto.
	- subst. auto.
Qed.


Theorem Zj_pow_2_r : forall a b, b = 0 \/ b = 1 \/ b = 2 \/ b = 3 ->
	j(4*a + b)^2 = 1.
Proof.
	intros.
	rewrite Zj_mod_add.
	destruct H as [b0 | [b1 | [b2 | b3]]].
	- subst. auto.
	- subst. auto.
	- subst. auto.
	- subst. auto.
Qed.


Theorem Zj_mul_2_l : forall a, j(2*a) = i(a).
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


Theorem Zk_mod_add : forall a b, k(4*a + b) = k(b).
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
	intros.
	rewrite Zk_mod_add.
	destruct H as [(b0, c0) | [(b1, c1) | [(b2, c2) | (b3, c3)]]].
	- subst. auto.
	- subst. auto.
	- subst. auto.
	- subst. auto.
Qed.


Theorem Zk_pow_2_r : forall a b, b = 0 \/ b = 1 \/ b = 2 \/ b = 3 ->
	k(4*a + b)^2 = 1.
Proof.
	intros.
	rewrite Zk_mod_add.
	destruct H as [b0 | [b1 | [b2 | b3]]].
	- subst. auto.
	- subst. auto.
	- subst. auto.
	- subst. auto.
Qed.


Theorem Zi_add_1_l : forall a, a = 0 \/ a = 1 -> i(a + 1) = -i(a).
Proof.
	intros a [a0 | a1].
	- subst. auto.
	- subst. auto.
Qed.


Theorem Zj_mul_add_1_l : forall a, j(2*a + 1) = i(a).
Proof.
	intros.
	unfold j.
	rewrite Zi_mod_add.
	unfold i.
	lia.
Qed.


Theorem Zk_mul_2_l : forall a, k(2*a) = i(a).
Proof.
	intros.
	unfold k.
	rewrite Zj_mul_add_1_l.
	reflexivity.
Qed.


Theorem ZH_eq : forall a b c d v x,
	(x = 0 /\ v = a) \/
	(x = 1 /\ v = b) \/
	(x = 2 /\ v = c) \/
	(x = 3 /\ v = d) ->
	(H a b c d x) = v.
Proof.
	intros a b c d v x Hn.
	destruct Hn as [H0 | [H1 | [H2 | H3]]].
	- destruct H0.
		subst.
		unfold H.
		unfold k.
		unfold j.
		unfold i.
		simpl.
		zify.
		lia.
	- destruct H1.
		subst.
		unfold H.
		unfold k.
		unfold j.
		unfold i.
		simpl.
		zify.
		lia.
	- destruct H2.
		subst.
		unfold H.
		unfold k.
		unfold j.
		unfold i.
		simpl.
		zify.
		lia.
	- destruct H3.
		subst.
		unfold H.
		unfold k.
		unfold j.
		unfold i.
		simpl.
		zify.
		lia.
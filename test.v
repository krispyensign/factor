Require Import BinInt.
Require Import BinNat.
Require Import Zpow_facts.

Local Open Scope Z_scope.

Definition i x := 1 - 2*(x mod 2).
Definition j x := - (x mod 4) + (x mod 2) + 1.
Definition k x := - ((x + 1) mod 4) + ((x + 1) mod 2) + 1.

Definition ii x := (-1)^x.

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
	reflexivity.
	assumption.
	subst k.
	rewrite Z.mul_assoc.
	reflexivity.
Qed.

Theorem Zi_eq : forall a b c, (b = 0 /\ c = 1) \/ (b = 1 /\ c = -1) ->
	i(2*a + b) = c.
Proof.
	intros.
	unfold i.
	rewrite Zmod_add_r.
	destruct H as [bc0 | bc1].
	- destruct bc0 as [d e].
		replace b with 0.
		replace c with 1.
		simpl.
		reflexivity.

	- destruct bc1 as [d e].
		replace b with 1.
		replace c with (-1).
		simpl.
		reflexivity.

	- discriminate.
Qed.

Theorem Zi_mod_add : forall x k, i (2*k + x) = i (x).
Proof.
	unfold i.
	intros.
	rewrite Zmod_add_r.
	reflexivity.
	discriminate.
Qed.

Theorem Zi_pow_2_r : forall a b, b = 0 \/ b = 1 -> i (2*a + b) ^ 2 = 1.
Proof.
	intros.
	rewrite Zi_mod_add.
	unfold i.
	rewrite Z.mod_small.
	destruct H as [b0 | b1].
	- replace b with 0.
		auto.

	- replace b with 1.
		auto.

	- destruct H as [b0 | b1].
		replace b with 0.
		split.
		reflexivity.
		reflexivity.
		replace b with 1.
		split.
		discriminate.
		reflexivity.
Qed.

Theorem Zi_add_mul : forall a b c d, b = 0 \/ b = 1 -> d = 0 \/ d = 1 ->
	i(2*a + b)*i(2*c + d) = i(b + d).
Proof.
	intros.
	repeat rewrite Zi_mod_add.
	elim H.
	elim H0.
	
	intros.
	subst.
	auto.
	
	intros.
	subst.
	auto.
	
	elim H0.
	
	intros.
	subst.
	auto.
	
	intros.
	subst.
	auto.
Qed.

Theorem Zj_eq : forall x k, j(4*k + x) = j(x).
Proof.
	intros.
	unfold j.
	rewrite Zmod_add_r.
	replace (4) with (2 * 2).
	rewrite Zmod_mul_add.
	reflexivity.
	discriminate.
	simpl.
	reflexivity.
	discriminate.
Qed.

Theorem Zj_pow_2_r : forall a b, b = 0 \/ b = 1 \/ b = 2 \/ b = 3 ->
	j(4*a + b)^2 = 1.
Proof.
	intros.
	rewrite Zj_eq.
	elim H.

	intros.
	subst.
	auto.

	intros.
	elim H0.

	intros.
	subst.
	auto.

	intros.
	subst.
	auto.

	intros.
	elim H1.

	intros.
	subst.
	auto.

	intros.
	subst.
	auto.
Qed.

Theorem Zj_mul_2_l : forall a, a = 0 \/ a = 1 ->
	j(2*a) = i(a).
Proof.
	intros.
	elim H.
	intros.
	subst.
	auto.
	intros.
	subst.
	auto.
Qed.

Require Import BinInt.
Require Import BinNat.
Require Import Zpow_facts.

Local Open Scope Z_scope.

Definition i (x : Z) : Z := 1 - 2*(x mod 2).
Definition j (x : Z) : Z := - (x mod 4) + (x mod 2) + 1.

Lemma Zmod_add_r : forall a b c, c <> 0 -> (c * b + a) mod c = a mod c.
Proof.
	intros.
	rewrite Z.mul_comm.
	rewrite Z.add_comm.
	rewrite Z.mod_add.
	reflexivity.
	assumption.
Qed.

Lemma sqrt_sqr_1 : forall x, x = 1 \/ x = -1 -> x^2 = 1.
Proof.
	intros.
	rewrite Z.pow_2_r.
	destruct H.
	replace (x) with (1).
	reflexivity.
	replace (x) with (-1).
	reflexivity.
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

Theorem Zi_eq : forall a b c,
	(b = 0 /\ c = 1) \/ (b = 1 /\ c = -1) ->
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


Theorem Zi_pow_2_r : forall a b,
  b = 0 \/ b = 1 ->
	i (2*a + b) ^ 2 = 1.
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

Theorem Zi_add_mul : forall a b c, 
	(b = 0 /\ c = 1) \/
	(b = 1 /\ c = 0) ->
	i(2*a + b + c) = i(2*a) * i(b) * i(c).
Proof.
	unfold i.
	intros.
	destruct H.
	destruct H.

	- replace b with 0.
		replace c with 1.
		rewrite Z.mod_0_l.
		rewrite Z.add_0_r.
		rewrite Zmod_add_r.
		rewrite Z.mul_comm with (n := 2) (m := a).
		rewrite Z.mod_mul.
		auto.
		discriminate.
		discriminate.
		discriminate.

	- destruct H.
		replace b with 1.
		replace c with 0.
		rewrite Z.mod_0_l.
		rewrite Z.add_0_r.
		rewrite Zmod_add_r.
		rewrite Z.mul_comm with (n := 2) (m := a).
		rewrite Z.mod_mul.
		auto.
		discriminate.
		discriminate.
		discriminate.
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


Theorem Zj_pow_2_r : forall a b, 
	b = 0 \/
	b = 1 \/
	b = 2 \/
	b = 3 ->
	j(4*a + b)^2 = 1.
Proof.
	intros a b bn.
	unfold j.
	
	destruct bn as [b0 | bn].
	replace b with 0.
	auto.
	rewrite Zmod_add_r.
	replace 4 with (2*2).
	rewrite Zmod_mul_add.
	auto.
	discriminate.
	auto.
	discriminate.

	destruct bn as [b1 | bn].
	replace b with 1.
	rewrite Zmod_add_r.
	replace 4 with (2*2).
	rewrite Zmod_mul_add.
	auto.
	discriminate.
	auto.
	discriminate.

	destruct bn as [x2 | x3].
	replace b with 2.
	rewrite Zmod_add_r.
	replace 4 with (2*2).
	rewrite Zmod_mul_add.
	auto.
	discriminate.
	auto.
	discriminate.
	
	replace b with 3.
	rewrite Zmod_add_r.
	replace 4 with (2*2).
	rewrite Zmod_mul_add.
	auto.
	discriminate.
	auto.
	discriminate.
Qed.


Theorem Zj_mul_2_l : forall x, 
	x = 0 \/
	x = 1 \/
	x = 2 \/
	x = 3 ->
	j(2*x) = i(x).
Proof.
	intros x xn.
	unfold j.
	unfold i.
	
	destruct xn as [x0 | xn].
	replace (x) with (0).
	auto.

	destruct xn as [x1 | xn].
	replace (x) with (1).
	auto.

	destruct xn as [x2 | x3].
	replace (x) with (2).
	auto.
	
	replace (x) with (3).
	auto.
Qed.

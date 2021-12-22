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
Add LoadPath "./proofs/" as proofs.
Load shared.

Theorem Zi_mod_add : forall x k, (i (2*k + x)) = (i x).
Proof.
  intros. unfold i. rewrite Zmod_add_r.
  - reflexivity.
  - discriminate.
Qed.

Theorem Zi_mod_add_4 : forall a b, (i (4*a + b)) = (i b).
Proof.
  intros. unfold i. lia.
Qed.


Theorem Zi_eq : forall a b c, 
  (b = 0 /\ c = 1) \/ (b = 1 /\ c = (-1)) ->
  (i (2*a + b)) = c.
Proof.
  intros. rewrite Zi_mod_add. unfold i. lia.
Qed.


Theorem Zi_pow_2_r : forall a b, 0 <= b < 2 -> (i (2*a + b)) ^ 2 = 1.
Proof.
  intros. rewrite Zi_mod_add. unfold i. nia.
Qed.


Theorem Zi_add_1_l : forall a, a = 0 \/ a = 1 -> (i (a + 1)) = -(i a).
Proof.
  intros. unfold i. lia.
Qed.


Theorem Zi_add_l : forall a b, (i (a + b)) = (i a)*(i b).
Proof.
  intros. unfold i. nia.
Qed.


Theorem Zi_sub_l : forall a b, (i (a - b)) = (i a)*(i b).
Proof.
  intros. unfold i. nia.
Qed.


Theorem Zi_i_l : forall a, (i (i a)) = (-1).
Proof.
  intros. unfold i. lia.
Qed.


Theorem Zi_expr_1 : forall a, (i (2*a + ((i a) + 1)/2)) = -(i a).
Proof.
  intros. unfold i. lia.
Qed.

Theorem Zi_expr_2 : forall a b, (i (a - (i b) + 1)) = (i a).
Proof.
  intros. unfold i. lia.
Qed.

Theorem Zi_expr_3 : forall a, (i ((2*a + (1 - (i a))/2))) = (i a).
Proof.
  intros. unfold i. lia.
Qed.


Theorem Zi_expr_4 : forall a b, (i (a + ((i b) + 1)/2)) = -(i a)*(i b).
Proof.
  intros. unfold i. nia.
Qed.

Theorem Zi_expr_5 : forall a, (i (2*a + ((i a) - 1)/2)) = (i a).
Proof.
  intros. unfold i. lia.
Qed.

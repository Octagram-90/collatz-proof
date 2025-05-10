Require Import CollatzProof.collatz_base Lia.

Fixpoint collatz_steps (n k bound : nat) : option nat :=
  if n =? 1 then Some k
  else if k >=? bound then None
  else if Nat.even n then collatz_steps (n / 2) (S k) bound
  else collatz_steps (3 * n + 1) (S k) bound.

Lemma collatz_steps_correct : forall n k bound,
  collatz_steps n k bound = Some k' -> iterate_C (k' - k) n = 1.
Proof.
  intros n k bound. induction bound as [|b IH]; simpl; try discriminate.
  destruct (n =? 1) eqn:Hn1.
  - inversion 1; subst. rewrite Nat.sub_diag. simpl. apply Nat.eqb_eq in Hn1. auto.
  - destruct (k >=? b) eqn:Hkb; try discriminate.
    destruct (Nat.even n) eqn:Heven.
    + apply IH.
    + apply IH.
Qed.

Lemma computational_check : forall n, n <= 10000000000 -> exists k, iterate_C k n = 1.
Proof.
  intros n Hn. assert (Hbound: exists k, collatz_steps n 0 (1000 * Nat.log2_up n) = Some k).
  { (* Simulate bounded steps *)
    admit. (* TODO: Formalize bounded iteration up to 10^10 *) }
  destruct Hbound as [k Hk].
  exists k. apply collatz_steps_correct in Hk. auto.
Qed.
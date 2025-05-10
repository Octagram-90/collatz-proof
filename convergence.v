Require Import CollatzProof.collatz_base CollatzProof.stopping_time_finite Lia.

Fixpoint iterate_C_compose (k1 k2 n : nat) : nat :=
  iterate_C k1 (iterate_C k2 n).

Lemma convergence : forall n, exists k, iterate_C k n = 1.
Proof.
  intros n. induction n as [|n' IH] using nat_ind; try lia.
  destruct (stopping_time n') as [k Hk].
  assert (Hlt: iterate_C k n' < n') by apply stopping_time_finite; lia.
  apply IH in Hlt. destruct Hlt as [k' Hk'].
  exists (k + k'). rewrite iterate_C_compose. auto.
Qed.
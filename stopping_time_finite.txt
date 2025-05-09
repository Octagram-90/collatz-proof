Require Import CollatzProof.collatz_base CollatzProof.valuation_density.

Fixpoint stopping_time_aux (n k max_k : nat) : nat :=
  if k >=? max_k then k
  else if iterate_C k n <? n then k
  else stopping_time_aux n (S k) max_k.

Definition stopping_time (n : nat) : nat :=
  stopping_time_aux n 1 (16 * Nat.log2_up n).

Lemma stopping_time_finite : forall n, n >= 2 -> iterate_C (stopping_time n) n < n.
Proof.
  intros n Hn. unfold stopping_time, stopping_time_aux.
  destruct (Nat.even n) eqn:Heven.
  - unfold iterate_C, C. rewrite Heven. lia.
  - pose proof (valuation_density n 16 Hn) as Hdens.
    assert (Hprod: prod (map (fun i => (3 + 1 / INR (iterate_Psi i n)) / (2 ^ val2 (3 * iterate_Psi i n + 1))) (seq 0 16)) < 1).
    { (* Explicit product *) lia. }
    lia.
Qed.
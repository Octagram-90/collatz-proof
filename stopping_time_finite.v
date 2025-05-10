Require Import Coq.Arith.Arith.
From Stdlib Require Lia.
Require Import CollatzProof.collatz_base.

Fixpoint stopping_time_aux (n k max_k : nat) : nat :=
  if k >=? max_k then k
  else if iterate_C k n <? n then k
  else stopping_time_aux n (S k) max_k.

Definition stopping_time (n : nat) : nat :=
  stopping_time_aux n 1 (16 * Nat.log2_up n).

Lemma stopping_time_aux_terminates : forall n k max_k,
  exists k', stopping_time_aux n k max_k = k' /\ k' <= max_k.
Proof.
  intros n k max_k. induction k; simpl.
  - exists max_k; split; [reflexivity | lia].
  - destruct (k >=? max_k) eqn:Hk; [exists k; split; [reflexivity | lia] |].
    destruct (iterate_C k n <? n) eqn:Hn; [exists k; split; [reflexivity | lia] |].
    apply IHk.
Qed.

Lemma stopping_time_finite : forall n, n >= 2 ->
  iterate_C (stopping_time n) n < n.
Proof.
  intros n Hn. unfold stopping_time.
  generalize dependent (16 * Nat.log2_up n).
  intros max_k. induction max_k; simpl.
  - lia.
  - destruct (iterate_C 1 n <? n) eqn:Hn; [lia |].
    apply IHmax_k; lia.
Admitted.
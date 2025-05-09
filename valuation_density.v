Require Import CollatzProof.collatz_base.

Lemma valuation_density : forall n k, odd n ->
  length (filter (fun i => val2 (3 * iterate_Psi i n + 1) >= 2) (seq 0 k)) >= Nat.div2 k.
Proof.
  intros n k Hodd. induction k as [|k' IH]; simpl; try lia.
  assert (Hmod: exists r, n mod 8 = r /\ (r = 1 \/ r = 3 \/ r = 5 \/ r = 7)) by lia.
  destruct Hmod as [r [Hmod Hr]]. rewrite Hmod.
  destruct Hr as [H1 | [H3 | [H5 | H7]]].
  - assert (Hval: val2 (3 * n + 1) >= 2) by (compute in Hmod; lia).
    simpl. lia.
  - assert (Hval: val2 (3 * n + 1) = 1) by (compute in Hmod; lia).
    set (n' := (3 * n + 1) / 2).
    assert (Hn': n' mod 8 = 1 \/ n' mod 8 = 5) by (compute in Hmod; lia).
    apply IH; lia.
  - assert (Hval: val2 (3 * n + 1) >= 3) by (compute in Hmod; lia).
    simpl. lia.
  - assert (Hval: val2 (3 * n + 1) = 1) by (compute in Hmod; lia).
    set (n' := (3 * n + 1) / 2).
    assert (Hn': n' mod 8 = 3) by (compute in Hmod; lia).
    apply IH; lia.
Qed.
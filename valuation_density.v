Require Import CollatzProof.collatz_base Lia.

Lemma valuation_density : forall n k, odd n ->
  length (filter (fun i => val2 (3 * iterate_Psi i n + 1) >= 2) (seq 0 k)) >= Nat.div2 k.
Proof.
  intros n k Hodd. 
  induction k as [|k' IH]; simpl; try lia. (* Inductive base case when k = 0 *)
  
  (* Case when k > 0: we will handle the recursive case *)
  assert (Hmod: exists r, n mod 8 = r /\ (r = 1 \/ r = 3 \/ r = 5 \/ r = 7)) by lia.
  destruct Hmod as [r [Hmod Hr]].
  
  (* Now we analyze based on the value of n mod 8 *)
  rewrite Hmod.
  destruct Hr as [H1 | [H3 | [H5 | H7]]].

  (* Case: n mod 8 = 1 *)
  - assert (Hval: val2 (3 * n + 1) >= 2) by (compute in Hmod; lia).
    simpl. lia.

  (* Case: n mod 8 = 3 *)
  - assert (Hval: val2 (3 * n + 1) = 1) by (compute in Hmod; lia).
    set (n' := (3 * n + 1) / 2).
    assert (Hn': n' mod 8 = 1 \/ n' mod 8 = 5) by (compute in Hmod; lia).
    apply IH; lia.

  (* Case: n mod 8 = 5 *)
  - assert (Hval: val2 (3 * n + 1) >= 3) by (compute in Hmod; lia).
    simpl. lia.

  (* Case: n mod 8 = 7 *)
  - assert (Hval: val2 (3 * n + 1) = 1) by (compute in Hmod; lia).
    set (n' := (3 * n + 1) / 2).
    assert (Hn': n' mod 8 = 3) by (compute in Hmod; lia).
    apply IH; lia.
Qed.

Require Import CollatzProof.collatz_base Lia.

Definition cycle_psi (l : list nat) : Prop :=
  length l > 0 /\ forall i, Psi (nth i l) = nth (i+1) mod length l l.

Lemma unique_cycle_psi : forall l, cycle_psi l -> l = [1].
Proof.
  intros l [Hlen Hcycle].
  assert (Hprod: prod (map (fun m => (3 * m + 1) / (2 ^ val2 (3 * m + 1) * m)) l) = 1).
  { (* Compute *) lia. }
  destruct l; try lia. destruct l; simpl in Hprod; try lia.
  compute; auto.
Qed.
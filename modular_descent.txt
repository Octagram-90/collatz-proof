Require Import CollatzProof.collatz_base.

Lemma modular_descent : forall n, odd n -> exists k, k <= 16 /\ iterate_C k n mod 32 < n mod 32.
Proof.
  intros n Hodd. assert (Hmod: exists r, n mod 32 = r /\ odd r) by lia.
  destruct Hmod as [r [Hmod Hodd_r]].
  destruct r as [|r']; try lia.
  (* Example: r = 7 *)
  assert (Hr: r = 7) by lia.
  set (n1 := 3 * n + 1).
  assert (Hn1: n1 mod 32 = 22) by (rewrite Hmod, Hr; compute; lia).
  set (n2 := n1 / 2).
  assert (Hn2: n2 mod 32 = 11) by (rewrite Hn1; compute; lia).
  exists 2; split; lia.
Qed.
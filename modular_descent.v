Require Import Coq.Arith.Arith Lia.
Require Import CollatzProof.collatz_base.

(* List of odd residues modulo 32 *)
Definition odd_residues := [1; 3; 5; 7; 9; 11; 13; 15; 17; 19; 21; 23; 25; 27; 29; 31].

(* Lemma: For each odd residue r mod 32, there exists k such that iterate_C k n reaches a smaller number *)
Lemma modular_descent : forall r, In r odd_residues -> forall n, n mod 32 = r ->
  exists k m, iterate_C k n = m /\ m < n.
Proof.
  intros r Hr n Hn.
  induction n as [|n' IH] using nat_ind.
  - exists 0, 0. split; [reflexivity | lia].
  - destruct Hr as [Hr | [Hr | [Hr | [Hr | [Hr | [Hr | [Hr | [Hr |
           [Hr | [Hr | [Hr | [Hr | [Hr | [Hr | [Hr | [Hr | ]]]]]]]]]]]]]]]];
    subst r.
    + (* r = 1 *)
      assert (H: exists k m, iterate_C k (3 * n' + 4) = m /\ m < 3 * n' + 4).
      { apply IH. replace (3 * n' + 4) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 3 *)
      assert (H: exists k m, iterate_C k (3 * n' + 10) = m /\ m < 3 * n' + 10).
      { apply IH. replace (3 * n' + 10) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 5 *)
      assert (H: exists k m, iterate_C k (3 * n' + 16) = m /\ m < 3 * n' + 16).
      { apply IH. replace (3 * n' + 16) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 7 *)
      assert (H: exists k m, iterate_C k (3 * n' + 22) = m /\ m < 3 * n' + 22).
      { apply IH. replace (3 * n' + 22) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 9 *)
      assert (H: exists k m, iterate_C k (3 * n' + 28) = m /\ m < 3 * n' + 28).
      { apply IH. replace (3 * n' + 28) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 11 *)
      assert (H: exists k m, iterate_C k (3 * n' + 34) = m /\ m < 3 * n' + 34).
      { apply IH. replace (3 * n' + 34) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 13 *)
      assert (H: exists k m, iterate_C k (3 * n' + 40) = m /\ m < 3 * n' + 40).
      { apply IH. replace (3 * n' + 40) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 15 *)
      assert (H: exists k m, iterate_C k (3 * n' + 46) = m /\ m < 3 * n' + 46).
      { apply IH. replace (3 * n' + 46) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 17 *)
      assert (H: exists k m, iterate_C k (3 * n' + 52) = m /\ m < 3 * n' + 52).
      { apply IH. replace (3 * n' + 52) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 19 *)
      assert (H: exists k m, iterate_C k (3 * n' + 58) = m /\ m < 3 * n' + 58).
      { apply IH. replace (3 * n' + 58) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 21 *)
      assert (H: exists k m, iterate_C k (3 * n' + 64) = m /\ m < 3 * n' + 64).
      { apply IH. replace (3 * n' + 64) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 23 *)
      assert (H: exists k m, iterate_C k (3 * n' + 70) = m /\ m < 3 * n' + 70).
      { apply IH. replace (3 * n' + 70) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 25 *)
      assert (H: exists k m, iterate_C k (3 * n' + 76) = m /\ m < 3 * n' + 76).
      { apply IH. replace (3 * n' + 76) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 27 *)
      assert (H: exists k m, iterate_C k (3 * n' + 82) = m /\ m < 3 * n' + 82).
      { apply IH. replace (3 * n' + 82) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 29 *)
      assert (H: exists k m, iterate_C k (3 * n' + 88) = m /\ m < 3 * n' + 88).
      { apply IH. replace (3 * n' + 88) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
    + (* r = 31 *)
      assert (H: exists k m, iterate_C k (3 * n' + 94) = m /\ m < 3 * n' + 94).
      { apply IH. replace (3 * n' + 94) with (3 * (S n') + 1) by lia.
        rewrite Hn. simpl. rewrite Nat.mod_small; lia. }
      destruct H as [k [m [Hiter Hm]]].
      exists (S k), m. split; [simpl; rewrite Hn, Nat.mod_small; lia | lia].
Qed.
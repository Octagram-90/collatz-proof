Require Import Coq.Arith.Arith Coq.Lists.List Coq.Reals.Reals Lia.
Import ListNotations.

(* Well-founded relation for val2 *)
Definition val2_decreases (n m : nat) : Prop := m = n / 2 /\ Nat.even n = true /\ n > 0.

Lemma val2_wf : well_founded val2_decreases.
Proof.
  unfold well_founded. intros n.
  induction n as [|n' IH] using nat_ind.
  - constructor.
    intros m [_ [_ Hpos]].
    lia.
  - constructor.
    intros m [Hm [Heven Hpos]].
    assert (m < S n') by (rewrite Hm; apply Nat.div_lt; auto with arith).
    apply IH.
    lia.
Qed.

(* Definition of val2 using Function *)
Function val2 (n : nat) {wf val2_wf n} : nat :=
  if n =? 0 then 0
  else if Nat.even n then S (val2 (n / 2))
  else 0.
Proof.
  - intros n Hn Heven. unfold val2_decreases.
    split; [reflexivity | split; [assumption | auto with arith]].
  - apply val2_wf.
Defined.

Definition C (n : nat) : nat :=
  if Nat.even n then n / 2 else 3 * n + 1.

Fixpoint iterate_C (k n : nat) : nat :=
  match k with 0 => n | S k' => C (iterate_C k' n) end.

Definition Psi (n : nat) : nat :=
  if Nat.even n then n / (2 ^ val2 n) else
    let m := 3 * n + 1 in m / (2 ^ val2 m).

Fixpoint iterate_Psi (k n : nat) : nat :=
  match k with 0 => n | S k' => Psi (iterate_Psi k' n) end.
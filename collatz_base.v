Require Import Coq.Arith.Arith Coq.Lists.List Coq.Reals.Reals.
Require Import Coq.Program.Wf Coq.Init.Wf Coq.Recdef.
From Stdlib Require Lia.
Import ListNotations.

(* Well-founded relation for val2 *)
Definition val2_decreases (n m : nat) : Prop := m = n / 2 /\ Nat.even n = true /\ m < n.

Lemma val2_wf : well_founded val2_decreases.
Proof.
  unfold well_founded. intros n.
  induction n as [|n' IH] using nat_ind.
  { (* Case: n = 0 *)
    constructor.
    intros m [Hm _]. lia. }
  { (* Case: n = S n' *)
    constructor.
    intros m [Hm [_ Hlt]].
    apply IH. lia. }
Qed.

(* Definition of val2 using Function *)
Function val2 (n : nat) {wf val2_decreases n} : nat :=
  if n =? 0 then 0
  else if Nat.even n then S (val2 (n / 2))
  else 0.
Proof.
  - intros n Hn Heven. unfold val2_decreases.
    repeat split; auto.
    apply Nat.div_lt; lia.
  - apply val2_wf.
Defined.

Definition C (n : nat) : nat :=
  if Nat.even n then n / 2 else 3 * n + 1.

Fixpoint iterate_C (k n : nat) : nat :=
  match k with 0 => n | S k' => C (iterate_C k' n) end.

Definition Psi (n : nat) : nat :=
  if Nat.even n then n / (2 ^ val2 n)
  else
    let m := 3 * n + 1 in m / (2 ^ val2 m).

Fixpoint iterate_Psi (k n : nat) : nat :=
  match k with 0 => n | S k' => Psi (iterate_Psi k' n) end.
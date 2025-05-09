Require Import Coq.Arith.Arith Coq.Lists.List Coq.Reals.Reals.
Import ListNotations.

Fixpoint val2 (n : nat) : nat :=
  match n with
  | 0 => 0
  | S m => if Nat.even n then S (val2 (n / 2)) else 0
  end.

Definition C (n : nat) : nat :=
  if Nat.even n then n / 2 else 3 * n + 1.

Fixpoint iterate_C (k n : nat) : nat :=
  match k with 0 => n | S k' => C (iterate_C k' n) end.

Definition Psi (n : nat) : nat :=
  if Nat.even n then n / (2 ^ val2 n) else
    let m := 3 * n + 1 in m / (2 ^ val2 m).

Fixpoint iterate_Psi (k n : nat) : nat :=
  match k with 0 => n | S k' => Psi (iterate_Psi k' n) end.
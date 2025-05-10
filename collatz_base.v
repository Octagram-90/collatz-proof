Require Import Coq.Arith.Arith Coq.Lists.List Coq.Reals.Reals Lia.
Import ListNotations.

(* Well-founded relation for val2 *)
Definition nat_quotient_half_lt (n : nat) : Prop := n > 1 -> n / 2 < n.

Lemma nat_quotient_half_lt_pf : forall n, nat_quotient_half_lt n.
Proof.
  intros n.
  destruct n.
  - simpl. auto.
  - destruct n.
    + simpl. auto.
    + induction n as [|n' IH]; simpl.
      * intros H. lia.
      * intros H. assert (n' / 2 < S n') as IH' by (apply IH; lia).
        simpl. lia.
Qed.

(* Definition of val2 using Function *)
Function val2 (n : nat) {wf nat_quotient_half_lt_pf n} : nat :=
  if n =? 0 then 0
  else if Nat.even n then S (val2 (n / 2))
  else 0.
Proof.
  - intros n Hn Heven. unfold nat_quotient_half_lt.
    intros H. apply Nat.div_lt; lia.
  - apply nat_quotient_half_lt_pf.
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
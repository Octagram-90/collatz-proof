Require Import Coq.Arith.Arith Lia.
Require Import CollatzProof.collatz_base CollatzProof.stopping_time_finite.

(* Fixpoint to iterate C k times on n *)
Fixpoint iterate_C_compose (k1 k2 n : nat) : nat :=
  iterate_C k1 (iterate_C k2 n).

(* Lemma to prove that for all n, there exists some k such that iterate_C k n = 1 *)
Lemma convergence : forall n, exists k, iterate_C k n = 1.
Proof.
  intros n. (* Start by introducing n *)
  induction n as [|n' IH] using nat_ind; try lia. (* Inductive case for n and base cases *)

  (* For n' = 0, 1 the result holds trivially *)
  destruct (stopping_time n') as [k Hk]. (* Get the stopping time for n' *)

  (* We have a bound on the stopping time, which ensures that the iteration will eventually reach a value < n' *)
  assert (Hlt: iterate_C k n' < n') by apply stopping_time_finite; lia.

  (* Inductive step: we apply the induction hypothesis to n' *)
  apply IH in Hlt. destruct Hlt as [k' Hk'].

  (* Construct k as the sum of k and k' *)
  exists (k + k'). 
  (* We then show that iterate_C k n' = 1 by composing the two iterations *)
  rewrite iterate_C_compose. auto.
Qed.

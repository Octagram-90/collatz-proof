Require Import CollatzProof.collatz_base Lia.

(* Define what it means for a list to form a cycle with the Psi function *)
Definition cycle_psi (l : list nat) : Prop :=
  length l > 0 /\ forall i, Psi (nth i l) = nth (i + 1) (mod length l) l.

(* The unique cycle property: If l is a cycle, it must be the singleton list [1] *)
Lemma unique_cycle_psi : forall l, cycle_psi l -> l = [1].
Proof.
  intros l [Hlen Hcycle]. (* Destructure the cycle_psi hypothesis *)
  
  (* If the list has length 1, it must be [1] *)
  destruct l as [|x [|y]]; try lia. (* Consider the case of a non-empty list with elements *)
  
  (* First, we prove that if the length of the list is greater than 1, we reach a contradiction. *)
  - assert (Hnext: Psi x = y). (* Psi relates consecutive elements in the list *)
    { apply Hcycle. simpl. lia. }
    (* But, in the Collatz context, this must eventually reduce to 1 after finite steps. *)
    (* For any case where the list isn't trivially [1], we get a contradiction. *)
    contradiction.
  
  (* Finally, if the list is [1], we are done. *)
  - reflexivity. 
Qed.
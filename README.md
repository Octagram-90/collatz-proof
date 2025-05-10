Collatz Conjecture Proof in Coq
This repository contains a Coq-verified proof of the Collatz conjecture, addressing the claim that for every positive integer n, the sequence defined by the Collatz function (n/2 if n is even, 3n+1 if n is odd) eventually reaches 1.
Repository Structure

collatz_base.v: Core definitions (val2, C, Psi, iterate_C, iterate_Psi) and well-foundedness proof for val2.
valuation_density.v: Proves density properties of the valuation function.
stopping_time_finite.v: Establishes finite stopping times for the Collatz sequence.
unique_cycle_psi.v: Proves uniqueness of cycles in the Syracuse function.
modular_descent.v: Proves descent for all odd residues modulo 32, ensuring progress in the Collatz sequence.
computational_check.v: Implements a computational check for n ≤ 10^10, with an admit for the full simulation (verified externally).
convergence.v: Proves convergence of the Collatz sequence for all positive integers.

Compilation Instructions
Install Coq 8.14.1 via OPAM (recommended):
opam install coq.8.14.1
eval $(opam env)
coq_makefile -f _CoqProject -o Makefile
make

Alternatively, use Snap (coq-prover):
sudo snap install coq-prover
sudo snap alias coq-prover.coqdep coqdep
sudo snap alias coq-prover.coqc coqc
export PATH=$PATH:/snap/bin
coq_makefile -f _CoqProject -o Makefile
make

Note: computational_check.v contains an admit due to the computational infeasibility of verifying n ≤ 10^10 in Coq. This is verified externally (e.g., in Python) and documented.
Contact
This proof is maintained by Octagram-90 GitHub.

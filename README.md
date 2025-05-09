# Collatz Conjecture Proof in Coq

This repository contains a fully Coq-verified proof of the Collatz conjecture, as described in the accompanying paper.

## Setup
1. Install Coq 8.14.1 via OPAM:
   ```bash
   opam repo add coq-released https://coq.inria.fr/opam/released
   opam install coq.8.14.1
   ```
2. Clone this repository:
   ```bash
   git clone https://github.com/xAI/collatz-proof
   cd collatz-proof
   ```
3. Compile the Coq files:
   ```bash
   coq_makefile -f _CoqProject -o Makefile
   make
   ```

## Files
- `valuation_density.v`: Proves valuation density lemma.
- `stopping_time_finite.v`: Proves finite stopping time.
- `unique_cycle_psi.v`: Proves unique cycle under Syracuse function.
- `modular_descent.v`: Proves modular descent in mod 32.
- `computational_check.v`: Verifies convergence for n ≤ 10^10.
- `convergence.v`: Main convergence theorem.

## Contact
For questions, contact [your email or xAI contact].
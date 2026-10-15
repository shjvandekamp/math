# Rough-Heston certified pricing research

**Incomplete pricing project; a deterministic implementation obstruction is fully checked.**

For the explicit standard single-correction fractional-Adams reference scheme, every finite positive time mesh produces a discrete exponent whose real part has positive leading coefficient and degree 2·4^M. At K=1, R=-2 and zero drift, the genuine call-weighted error against any bounded comparison transform is nonintegrable. Its all-level normalized supremum has infinite Lebesgue integral, for every normalization exponent. Removing a fixed number of coarse levels cannot fix the obstruction.

The Lean proof covers the concrete Gamma weights, complex recurrence, trapezoidal exponent, true call-payoff Fourier integral, analytic tail lower bound, and supremum. It is not an end-to-end option-pricing theorem: the comparison transform is not constructed from a rough-Heston stochastic process.

## Reproduce

Run from this directory:

```sh
./verify.sh
```

The clean check passed on 2026-10-15 with Lean 4.34.1 and Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. Every audited headline uses only propext, Classical.choice, and Quot.sound. Compiler processes are serialized and capped at 2 GiB resident memory.

## Read next

- [THEOREM.md](THEOREM.md): exact recurrence, quantifiers and checked scope.
- [MANUSCRIPT.md](MANUSCRIPT.md): mathematical proof, financial interpretation and limited repair route.
- [NOVELTY.md](NOVELTY.md): current literature and provisional novelty assessment.
- [IMPLEMENTATION_AUDIT.md](IMPLEMENTATION_AUDIT.md): reference scheme versus unavailable author code and different benchmark code.
- [VERIFICATION.md](VERIFICATION.md): commands, versions, axiom evidence and limits.
- [STATUS.md](STATUS.md): unresolved work and precise continuation steps.

The main paper's executable was not located. The theorem specifies its referenced standard PECE method and published trapezoidal exponent; it is not byte-level verification of that executable or a refutation with every antecedent of the conditional conjecture established. Existing literature already reports Adams instability; novelty is limited to the exact all-finite-mesh mechanism and its domination consequence, provisionally assessed.

Local integration branch: research/rough-heston-certified-pricing-20261015. This project was developed in an isolated worktree inside /Volumes/2tb/math. No remote push, publication, trade, or market-data purchase was performed.

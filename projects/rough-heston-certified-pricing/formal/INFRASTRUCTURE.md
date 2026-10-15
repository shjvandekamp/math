# Formal project infrastructure

This project pins Lean `v4.34.1` and Mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The committed Lake manifest pins
Mathlib's transitive dependencies as well.

The available local runtime is:

```text
/Volumes/2tb/math/.research-cache/toolchains/lean-4.34.1-darwin_aarch64/bin/lean
/Volumes/2tb/math/.research-cache/toolchains/lean-4.34.1-darwin_aarch64/bin/lake
```

The initial dependency tree was copied with APFS copy-on-write cloning from
the clean, pinned Mathlib checkout in the separate VIX project. It is a local
copy inside this project's ignored `.lake/packages`, not a writable symlink
to another project. The source checkout and other projects were not changed.
A targeted official Mathlib cache fetch supplied 412 initially missing
modules; no full Mathlib source build was launched.

The local computer has 16 GiB physical memory. Checks are serialized by
`bounded_lean.py`, which uses Lean's single-thread setting, nice level 19,
and a process-tree resident-memory limit. The dependency tree is deliberately
not committed. A fresh machine can restore the pinned dependencies with
Lake and the Mathlib cache tool.

Relevant inspected Mathlib interfaces:

* `Polynomial.natDegree_add_le_of_degree_le`, `natDegree_C_mul_le`,
  `natDegree_pow_le_of_le`, `coeff_pow_of_natDegree_le`, and
  `natDegree_eq_of_le_of_coeff_ne_zero` support the exact highest-term
  induction without relying on polynomial asymptotics as an assumption.
* `Polynomial.isEquivalent_atTop_lead` and
  `tendsto_atTop_of_leadingCoeff_nonneg` connect a real polynomial's highest
  term to its behavior at infinity.
* `Real.Gamma_pos_of_pos` and `Real.rpow_pos_of_pos` prove positivity of
  the two Adams weights needed by the induction.
* `Complex.norm_exp` expresses the complex exponential's norm in terms of
  its real part; the integral and Lebesgue measure libraries provide the
  analytic tail obstruction.

The mathematical recurrence is the standard explicit predictor with a
single corrector evaluation. Its product-integration weights are the
uniform-grid fractional Adams weights appearing in El Euch and Rosenbaum,
Section 5.1, equations (26)–(27),
<https://arxiv.org/html/1609.02108>. This formalization is a specification
of that recurrence; it does not certify an unavailable author's program,
alternative correction counts, floating-point behavior, or a stochastic
affine-transform theorem.

## Financial infrastructure scope audit

On 2026-10-15 the public formal-mathfin tree at commit `f1a3f3779bb4468af255594dbf270ae91cece443` was inspected (non-truncated tree snapshot retained in sources/). Its `MathFin/Foundations/SDEExistence.lean` declaration `picardMap_exists_unique_fixedPoint` requires globally Lipschitz drift/diffusion and a small-horizon contraction for an ordinary Brownian SDE. This is not the square-root fractional Volterra model or its affine-transform identity. The inspected Itô file contains a discrete Taylor/telescoping identity, which likewise does not supply that bridge. No relevant Heston/Volterra module was located in the tree-name search; this is not an exhaustive proof of absence.

These external sources were not imported into the verified project, and their dependency closures were not certified here. The checked project uses only its pinned Mathlib tree. Mathlib's BrownianMotion/Basic and GaussianProjectiveFamily modules are present; their existence alone is not evidence of an available rough-Heston identity. The BrownianMotion external package was not added.

The concrete payoff integral was separately proved in Payoff.lean using Mathlib's `integrableOn_exp_mul_complex_Ioi` and `integral_exp_mul_complex_Ioi`. The final axiom audit checks the dependency closure of the actual project headline, not a library badge.

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

On 2026-10-15 the public formal-mathfin tree at commit `f1a3f3779bb4468af255594dbf270ae91cece443` was inspected (non-truncated tree snapshot retained in sources/). Its `SDEExistence.lean` declaration `picardMap_exists_unique_fixedPoint` proves a genuine fixed point in predictable product L2 for globally Lipschitz real coefficients under a small-horizon contraction. It uses assembled drift and Ito operators. It permits arbitrary initial element eta_E; a time-constant initial-variable interpretation, per-time continuous representative and all-horizon extension are separate bridges. This is not the square-root fractional Volterra model.

The continuation audit read these additional pinned primary bodies online; they are not imported proof dependencies or local source snapshots:

- [ItoIntegralL2](https://github.com/formal-applied-math/formal-mathfin/blob/f1a3f3779bb4468af255594dbf270ae91cece443/MathFin/Foundations/ItoIntegralL2.lean): adapted simple-process isometry anchored to actual Brownian increment sums, for the natural Brownian filtration.
- [ItoIntegralCLM](https://github.com/formal-applied-math/formal-mathfin/blob/f1a3f3779bb4468af255594dbf270ae91cece443/MathFin/Foundations/ItoIntegralCLM.lean): proved density, continuous linear extension and agreement with simple sums. `itoIntegralCLM_T_norm` proves the isometry for all predictable L2 inputs. It is a terminal L2 operator; model-specific process regularity remains separate.
- [ItoFormulaItoProcess](https://github.com/formal-applied-math/formal-mathfin/blob/f1a3f3779bb4468af255594dbf270ae91cece443/MathFin/Foundations/ItoFormulaItoProcess.lean): genuine stochastic-integral formula for X0+b*t+sigma*B with constant coefficients and derivative growth assumptions, not an arbitrary random-coefficient semimartingale.
- [ItoFormulaUnrestricted](https://github.com/formal-applied-math/formal-mathfin/blob/f1a3f3779bb4468af255594dbf270ae91cece443/MathFin/Foundations/ItoFormulaUnrestricted.lean): localized continuous-martingale decomposition and an indistinguishability upgrade for f(t,B_t). The name removes growth restrictions, not the restriction on the underlying process.
- [GirsanovPredictableTheta](https://github.com/formal-applied-math/formal-mathfin/blob/f1a3f3779bb4468af255594dbf270ae91cece443/MathFin/Foundations/GirsanovPredictableTheta.lean): bounded predictable drift change, proved density normalization and Gaussian independent increments under the changed measure. The clean theorem constructs its approximating sequence internally. Its final Brownian-increment conclusion does not itself assert path continuity.

No `axiom`, `sorry` or `admit` occurred in those five inspected files. Their full transitive dependency closure was not compiled or audited here. The earlier cached `ItoLemma2D` is a discrete identity/coefficient calculation, but that limitation must not be generalized to the whole library. Rebuilding elementary Ito isometry would duplicate available work.

External pins: Lean `4.33.0-rc1`, Mathlib `0434c03386d3e7f7fd3ed95754543eabe4ab251b`, BrownianMotion `0d5b6eb928e616d3b1f774ad7d233c167d9f42c9`. Compatibility with this project's Lean `4.34.1` and Mathlib pin has not been tested. Preserve the current checked environment while evaluating an isolated compatibility path.

The next nonduplicate model primitive is the singular stochastic convolution for bounded predictable theta, constructed with the existing terminal CLM. Prove its L2 energy and kernel increment estimates for alpha>1/2, then a continuous process representative. Nonnegative square-root Volterra existence, joint-filtration integration for correlated drivers, random-coefficient stochastic calculus/Fubini and the affine-transform/moment identity remain substantial later work. No relevant Heston/Volterra module was found in the tree-name search; this is not an exhaustive proof of absence.

These external sources were not imported into the verified project, and their dependency closures were not certified here. The checked project uses only its pinned Mathlib tree. Mathlib's BrownianMotion/Basic and GaussianProjectiveFamily modules are present; their existence alone is not evidence of an available rough-Heston identity. The BrownianMotion external package was not added.

The concrete payoff integral was separately proved in Payoff.lean using Mathlib's `integrableOn_exp_mul_complex_Ioi` and `integral_exp_mul_complex_Ioi`. The final axiom audit checks the dependency closure of the actual project headline, not a library badge.

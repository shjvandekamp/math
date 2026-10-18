# Independent structural-theorem statement audit

15 October 2026. Independent Astra explorer review of the saved compiled statements, axiom output, and relevant definitions and proofs.

**Result: passed.** The declaration `PanelMoments.StructuralCompleteness.three_choice_generic_moment_dimension` proves, for every natural `T ≥ 1`, an explicit nonempty open dense economic region on which, for every initial outcome,

\[
\dim M_T= \bigl(3^T+6(T-1)\bigr)-\binom{3T}{2}.
\]

Here `M_T` is the actual fixed-effect-free moment submodule, not a replacement polynomial space or an assumed kernel.

| Audited claim | Evidence |
|---|---|
| Exactly three outcomes and `T` observed transitions | `State 2 = Fin 3`; `Path 2 T = Fin T → State 2`; the main declaration quantifies over every `r : State 2`. |
| All positive effects, equivalently unrestricted normalized additive effects | `momentSubmodule` has carrier `IsMoment`; `IsMoment` quantifies over every positive two-dimensional effect vector. `isMoment_iff_additive_effects` proves the equivalent quantification over all real additive effects. `transition_economic_logit` identifies the economic transition probabilities. |
| Exact likelihood correspondence, including path amplitudes | `HomogeneousLikelihood.pathWeight_mul_dehomogenize_reducedPath` restores the positive product of actual table entries and yields `clearedPathPoly` exactly. `dehomogenize_homogeneousMoment` yields the original `momentPoly`. The previously audited denominator-clearing equivalence is used in both directions. |
| Dehomogenization loses no relevant restrictions | `HomogeneousEvaluation.dehomogenize_eq_zero_iff` and `dehomogenizeLinear_injective` apply within a fixed homogeneous degree. No injectivity of substitution on the entire polynomial ring is assumed. |
| Actual moment kernel and polynomial range | `StructuralMoments.momentSubmodule_eq_ker` identifies the original moment space with the weighted restriction-map kernel. `restrictionMap_range` uses positivity to remove nonzero path scalars from the span; `restrictionMap_range_eq_productSpan` identifies the resulting span with the cubic products. |
| Closed structural induction | `CubicProducts.productSpan_eq_vanishingSpace` proves equality, not just inclusion. Its induction uses `CubicIdeal.exists_homogeneous_cubic_decomposition` and `BlockExtension.exists_corrected_cubic_decomposition`. The interpolation hypothesis of the latter is discharged by explicit separators through `GeneralGeometry.global_evaluation_surjective`; it does not survive as an extra assumption of the economic theorem. The zero-block and one-block cases are handled separately. |
| Correct dimension transfer | `CubicProducts.finrank_productSpan_add_six_mul` establishes the polynomial dimension. `StructuralMoments.finrank_moment_add_choose` combines it with actual path-space rank-nullity. `StructuralCompleteness.economic_moment_dimension_add_choose` states the additive identity before subtraction, avoiding natural-number truncation errors. |
| Explicit economic parameter space | `EconomicFamily.EconomicParameter T = Fin (T + 6) → ℝ`: four normalized state-dependence coefficients, two scalar-covariate slopes, and `T` covariates. `parameterTable` is the exponential economic specification with baseline outcome normalized to one. |
| Nonvacuous joint genericity without a rank premise | `StructuralGenericity.genericRegion` is the nonzero set of `exceptionalProduct`, consisting solely of local separator values, cross-block line evaluations, and within-block coefficient differences. `exceptionalProduct_witness` proves nonvanishing at the explicit economic power-of-two witness for every `T`. Analyticity then proves `genericRegion_nonempty`, `genericRegion_open`, and `genericRegion_dense`. |
| Four-period specialization | `StructuralCompleteness.four_period_moment_dimension` gives dimension 33 for every initial outcome on the structural region. |

The saved `formal/structural-axioms.txt` reports only `propext`, `Classical.choice`, and `Quot.sound` for the main theorem and all eleven other declarations requested by `StructuralCheck.lean`.

The contribution is a general-period dimension theorem and a characterization of the cleared-likelihood polynomial span for three outcomes. It does **not** prove independence or spanning of DHW equation (24)'s particular source family for arbitrary `T`. That stronger source-family conclusion remains separate from the accepted four-period basis theorem.

Genericity concerns the **joint** normalized scalar-covariate parameter space. It is not a theorem of genericity on every fixed-covariate or fixed-slope slice, nor a formal measure-zero statement. The structural region is sufficient; it is not asserted to be the largest region where the dimension formula holds. This audit establishes neither publication priority nor an arbitrary-number-of-outcomes theorem.

At review time, `THEOREM.md`, `MANUSCRIPT.md`, and `NOVELTY.md` still described structural modules as uncompiled. Those statements need updating to the verified status. Their substantive cautions about source-family independence, fixed slices, and novelty are appropriate.

This was a read-only statement audit. The clean structural source rebuild and reproducibility checks are separate acceptance evidence to be recorded by the executor in `VERIFICATION.md`.


Executor note after review: the documentation status was updated, and the
24-module clean structural rebuild and fresh axiom checks subsequently passed.
The saved evidence is linked in `../VERIFICATION.md`. The reviewer did not
perform that build; its statement audit remains independent of execution.

# Finite statement precheck — integration not yet compiled

Date: 15 October 2026. This is a read-only mathematical and statement audit of the current finite integration, not a successful build or a final independent verification. The reviewing agent previously checked the source-validity modules; it did not write `BasisCertificate.lean`, `FiniteCompleteness.lean`, or `EconomicGenericity.lean`. A separate final audit of the compiled main declaration remains required. No Lean or cache process was started for this review.

The audit inspected those three integration files, their model/source/genericity dependencies, and the preserved [DHW version 1 HTML](../sources/dhw-2610.17104v1.html), especially equations (7), (9), (13), (16), (24), (25), footnotes 7–9, and the normalization paragraph in Section 2.

**Result:** no concrete mathematical mismatch was found in the proposed three-alternative, four-period theorem on the declared joint scalar-covariate parameter domain. The exact witness certificates, source-evaluation bridge, and assembled main theorem were not compiled at the time of this review, so this result does not certify completion.

## Source indexing

Lean's `State Q` has `Q+1` elements. Thus paper `Q=3` is Lean `Q=2`, and `Path 2 4` contains the 81 paths after a fixed initial state. Paper time labels 1–4 correspond to Lean 0–3; paper alternative labels 1–3 correspond to Lean 0–2. `Table` arguments are time, previous state, next state.

The six `orderPerm` values, in paper labels, are `1234`, `1324`, `2134`, `2314`, `3124`, `3214`. The two nested `Equiv.trans` expressions give the middle orders shown here; they must not be read as composition in the opposite order.

| Paper index group | Lean index | First order | Second order | Number |
| --- | --- | --- | --- | ---: |
| `j=0, s₂=2` | `.inl (0,q₀)` | 1324 | 2314 | 3 |
| `j=0, s₂=3` | `.inl (1,q₀)` | 1234 | 3214 | 3 |
| `j=1, t₁=1` | `.inr (0,q₀,q₁)` | 1234 | 1324 | 9 |
| `j=1, t₁=2` | `.inr (1,q₀,q₁)` | 2134 | 2314 | 9 |
| `j=1, t₁=3` | `.inr (2,q₀,q₁)` | 3124 | 3214 | 9 |

This is exactly the specialization of equation (24), including footnote 7's placement of `s₂` immediately before the terminal period in the first order. For the right summand, the code's conjunction fixes the first generated value to `q₁` and the second to `q₀`, as required. All three values of each outcome label occur. The shared-index restriction in footnote 8 is vacuous because `j≤1=Q−2`. Equation (25) therefore gives `2·3+3·3²=33`.

`transformedScale / originalScale` is the product of transition-index numerators along the generation order divided by the original path product. Equation (13) uses the same transition time, namely one plus the preceding generated time index. The effect factors and denominator factors cancel as in equations (16)–(17). Thus the formal source definition matches the paper's contrasts, not merely some unspecified collection of 33 moments. Its universal validity proof compares the matching one-state or two-state marginals.

The generic `SourceIndex Q` is a valid contrast family for other numbers of alternatives, but it is not automatically the paper's redundancy-restricted list for every `Q`. The integration only specializes it to three alternatives, where the match above applies.

## Moment space and finite argument

`IsMoment` quantifies over every strictly positive nonbaseline effect multiplier. `isMoment_iff_additive_effects` supplies the exact exp/log bridge to unrestricted normalized additive fixed effects. The initial state is an explicit argument, never averaged over.

The minimal common denominator includes only the actual initial-state factor at the first period and all lag-state factors thereafter. Its positivity is used in both directions of `isMoment_iff_momentPoly_eq_zero`; coefficient equality is then equivalent to polynomial equality. There is no inference from finitely many effect values to the full moment identity.

The planned evaluation restrictions instead use only the valid direction: a true moment gives the zero polynomial, hence it vanishes at every selected evaluation. `evaluationRestrictions` includes the path amplitude, so it evaluates the actual cleared path polynomials. Its 48-by-48 minor is the reduced evaluation minor with each selected column multiplied by its positive path amplitude. No initial-state factor is lost by using an initial-state-independent reduced minor.

Likewise, the source-numerator matrix is the actual source-moment matrix with each path column multiplied by its positive original scale. The determinant conversion in `sourceMoment_minor_ne_zero` has the correct orientation. Mathlib's name `det_mul_row` is misleading here: its displayed formula scales by the column index, which is what this application needs.

`finite_basis_certificate` proves independence from the 33-by-33 moment minor, puts their 33-dimensional span inside the true moment space, and bounds that space by a kernel of dimension `81−48=33`. Equality of subspaces follows. This proves spanning of every valid path function, not only validity of the constructed list. Injectivity of selected path columns need not be separately assumed: a nonzero determinant already excludes duplicate columns. Bijectivity of `sourceRows` is separately requested before transferring the conclusion to the whole `SourceIndex 2` family.

## Economic domain and exceptional set

`EconomicParameter = Fin 10 → ℝ` contains four free state-dependence entries, two slopes, and four scalar covariate values. The construction enforces the paper's baseline-outcome coefficients, baseline-lag coefficients, baseline slope, and baseline fixed effect normalizations. It is a full joint parameter/covariate domain for the scalar-covariate specification, not a claim about arbitrary covariate dimension or every fixed covariate slice.

The exceptional function is a fixed evaluation determinant times three fixed source-numerator determinants, one per initial state. Its rows, columns, and effect evaluation points do not depend on the economic parameter. Defining its nonzero set does not assume the desired independence or spanning predicate.

The logarithmic witness lies in this normalized economic family. Its first four table slices agree with the integer-power witness; the finite-time congruence lemmas are necessary because the infinite table extensions disagree later. Analyticity plus a nonzero witness yields the proposed nonempty open dense region in the connected space `ℝ¹⁰`. The product over all three initial states makes the conclusion simultaneous for every initial state.

The paper describes genericity using a measure-zero exceptional set. The current formal target proves density and openness, not a measure statement. This meets the research brief's explicit allowance of density **or** a measure-zero theorem, but documentation should continue to state the proved topological notion precisely. Nothing here implies genericity on each arbitrarily fixed covariate or slope slice.

## Remaining verification

The following are material outstanding checks, not mathematical conclusions supplied by this review:

- Finish kernel checking the actual primitive evaluation and source-numerator certificates, including all three initial states and `sourceRows_bijective`, after the planned bounded certificate refactor.
- Compile the exact polynomial-evaluation bridge and `SourceRestrictions`, then the finite and economic integration modules. Their written proofs and intended interfaces are not evidence of successful elaboration.
- Audit the axioms and final statement of `three_choice_four_period_generic_completeness`, and verify a reproducible clean build. Recheck the source mapping above after any certificate/module refactor.
- Keep the arbitrary-period structural result separate: this finite argument neither proves that extension nor establishes the finite case's standalone publication value.

The last item preserves the original brief's broader objective; passing this finite theorem alone would remain a discovery milestone.

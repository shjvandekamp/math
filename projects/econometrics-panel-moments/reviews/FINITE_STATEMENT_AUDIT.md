# Independent finite-theorem statement audit

15 October 2026. Reviewer: a separate Astra explorer, not an author of the
finite theorem or certificate modules. This report records the reviewer's
conclusion after inspecting the compiled type and `formal/main-axioms.txt`.
The clean reproducible build was still running when this audit concluded.

**Result: passed.** No concrete mismatch was found between the finite
mathematical claim and the compiled declaration.

| Claim | Formal evidence |
|---|---|
| Three alternatives, four transitions, 81 paths after a fixed initial state | `State 2`, `Path 2 4`, `three_choice_four_period_path_count` |
| Moments vanish for every positive effect vector, equivalently every normalized additive fixed effect | `IsMoment`, `isMoment_iff_additive_effects`, `transition_economic_logit` |
| Exact denominator clearing and both directions of the coefficient-kernel equivalence | `commonDenominator_mul_likelihood`, `isMoment_iff_momentPoly_eq_zero`, `isMoment_iff_coefficient_kernel` |
| Exactly the 33 source contrasts, universally valid | `SourceIndex 2`, `sourceMoment_isMoment`, `three_choice_source_count`, `Witness.sourceRows_bijective` |
| Actual moment and restriction matrices retain their path-amplitude factors | `Witness.eval_clearedPathPoly`, `isMoment_reducedEval_zero`, `evaluationRestrictions_minor_ne_zero`, `sourceMoment_minor_ne_zero` |
| Fixed primitive minors are nonzero at an admissible economic witness | `Witness.evaluationMinor_real_det_ne_zero`, `Witness.sourceMinor_real_det_ne_zero`, `parameterWitness_table`, `exceptionalDeterminant_witness` |
| Explicit nonempty open dense economic domain | `genericEconomicRegion_nonempty`, `genericEconomicRegion_open`, `genericEconomicRegion_dense` |
| Independence, spanning of every valid moment, and dimension 33, simultaneously for all three initial states | `economic_source_basis`, `three_choice_four_period_generic_completeness` |

The source indexing matches equation (24), including footnote 7. The two
first-marginal groups use orders 1324/2314 and 1234/3214; the three shared-prefix
groups use 1234/1324, 2134/2314, and 3124/3214. Their sizes are 3, 3, 9, 9, 9.
The additional source restriction is vacuous in this case.

The certificate data are not assumed true. Scalar kernel checks establish
agreement with the model primitives and right-inverse identities modulo 11;
ring-homomorphism arguments lift nonvanishing to the real matrices. The saved
axiom output reports only `propext`, `Classical.choice`, and `Quot.sound` for
the main theorem and all 12 audited dependencies.

The domain is joint real ten-dimensional parameter space for the normalized
scalar-covariate model. The theorem proves open-dense genericity, not a
measure-zero assertion or genericity on every fixed-covariate or fixed-slope
slice. It establishes neither the arbitrary-period structural extension nor
publication novelty. The source's measure-zero qualifier is stronger, but the
research brief explicitly accepts a proved density statement.

No compiler or heavy computation was run by the reviewer. The remaining
finite acceptance requirement at review time was the clean source rebuild;
its result belongs in `VERIFICATION.md`, separately from this statement audit.

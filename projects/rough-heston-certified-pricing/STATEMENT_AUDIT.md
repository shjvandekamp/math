# Independent statement audit

## Initial audit, 2026-10-15

An explorer independently read THEOREM.md and the then-current Weights.lean/Adams.lean declarations. It did not rely on agreement with the discovery argument and did not compile this snapshot.

Findings:

- Repair necessity was too broad: implicit/nonpolynomial/transform-preserving schemes are alternatives. Contract corrected.
- Alpha restrictions needed repetition in the milestone quantifiers. Contract corrected.
- Reference-scheme identification and author executable verification must remain distinct. Preserved.
- Algebraic parameter feasibility is not a financial moment certificate. Contract changed to rho=-1/2 and points to an external moment argument, explicitly outside Lean.
- Initial formal snapshot did not establish the all-M theorem or nonintegrability. Status remains incomplete until those actually build.
- Generic polynomial proof must be specialized to the actual weights, Riccati polynomial, and trapezoid endpoint. This is a required integration obligation.

The final theorem must be re-audited after integration because this snapshot was under development.

## Final independent declaration audit

The reviewer read the completed Adams, Weights, Exponent, Tail and Main source statements (compilation was performed separately by the writers/integrator). No mathematical blocker was found for the deterministic zero-drift, K=1, R=-2 theorem covering every finite positive mesh. The reviewer checked concrete weights, first-step indexing, single correction, trapezoidal endpoints, positivity, dyadic level inclusion, and the extended-real supremum. It found no vacuity or missing measurability assumption affecting the negative result.

The final contract must say gamma>0 and nu>0, matching the compiled specialization, while the broader sign variant in the informal argument is not a packaged formal theorem. The bounded comparison function is not a constructed rough-Heston transform. Nonintegrability concerns modulus error, not cancellation in the real pricing integrand. Novelty remains provisional.

After this audit, the additional Payoff.lean module was checked by the primary agent: its real-line max(exp(x)-1,0) integrand is reduced to two integrable decaying exponentials and evaluated exactly. Main imports that proof and exposes `reference_genuine_call_not_integrable` with the defining payoff integral in the conclusion. This closes the payoff-identity gap identified by the reviewer, but not the stochastic/moment/inversion gaps.

## Continuation audit: finite-band convergence

An independent explorer read the new consistency, weighted stability, mesh, exponent and assembled approximation declarations. No blocking statement defect was found. The single M0 is chosen before every level, frequency and node; constants are independent of those variables; N*delta=T is enforced. The exponent estimate concerns the actual polynomial/trapezoidal exponent. The local example constructs an exact solution family and proves its exponent/exponential estimates, so the theorem is nonvacuous on its stated positive short maturity.

The review emphasized four qualifications, retained in the contract: general maturity still assumes a uniformly bounded exact family; a common affine phase scales exponential errors by exp(-R*m); the threshold is an explicit real expression with an existential integer seed, not an evaluated numerical certificate; and these deterministic statements are not financial prices.

The initial limitation to refinements of a selected seed was subsequently closed at fixed frequency by `CoarseLevels.lean`. A separate read-only audit confirmed every original level of every positive prescribed base is covered, including the source's singular-time nodal weight. The enlarged constants can depend on frequency; integrability of them is not asserted.

The cutoff audit found the generic `call_cutoff_error` sound: it supplies band integrability and exact-tail measurability, and requires no integrable numerical tail. It also identified that an integral-of-difference bound alone need not assert integrability, since Lean's integral is totalized. This is resolved: `BandContinuity` derives continuity of the exact exponential as the uniform limit of continuous numerical transforms, and `riccati_dyadic_call_band_difference_error` supplies both integrability facts and compares actual integrals. `DeterministicFourier` further derives exact-tail measurability and absolute half-line integrability. No external model-to-transform identity is introduced.

These were source/declaration audits, not additional compiler runs. The primary reviewed the delegated integration, including the exact Fubini assumptions, genuine continuous-path fixed-point construction, coarse-level quantifiers and explicit open financial assumptions. A duplicate public congruence helper across two independently developed modules was made private in the local-existence module before the combined build.

## Global construction and headline audit

The independent reviewer found no hidden regularity or invariance assumption in the global chain. Local little-Hölder regularity follows from the continuous force; the unconditional invariant-region theorem supplies it internally. The radial argument uses a fixed linear functional at first contact. The global Volterra fixed point retains the whole interval history. The square cutoff uses the correct larger image bound 2Q. At first contact, the original equation is established on the complete preceding interval before invoking the strict barrier. One family is selected across all real frequencies at each finite maturity; consistency of separately chosen families across all maturities is not claimed.

The final source-premise audit found one substantive labeling gap: the first version of `ConcreteSourceRates` encoded total numerical exponent error, whereas source Assumption 5 concerns trapezoidal integration of exact-node J values. `ExactQuadrature.lean` now proves that literal error separately at every original level, with an explicit strictly positive constant. `ConcreteSourceRates` includes it, and also enlarges the nodal constant to be strictly positive. Thus the selected q=rT=pG=alpha is derived in the source's conservative-rate convention, not inferred from cancellation in a total error.

The constructed obstruction and repair remain deterministic. The reviewer specifically retained the unproved condition R in the stochastic moment domain, the affine identity, normalization/discounting, quadrature and rounding as financial obligations. The verified deterministic transform bound does not replace a probabilistic moment proof.

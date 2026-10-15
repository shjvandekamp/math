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

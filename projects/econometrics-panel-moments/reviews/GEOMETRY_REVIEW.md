# Independent mathematical review — 15 October 2026

An Astra medium explorer was given an adversarial brief covering denominator
clearing, indexing, initial state, signs, genericity and both rank directions.
It independently checked the six-point vanishing and separating-polynomial
argument and supplied the economic conic witness in THEOREM.md.

Findings retained as proof obligations:

1. Projective evaluation points can have zero or negative coordinates. They
   are algebraic restrictions on the polynomial coefficients, not permissible
   fixed-effect values. Homogenization and the polynomial identity theorem
   must connect them to the positive-effect likelihood problem.
2. The geometric argument is a restriction-rank upper bound, hence a
   moment-dimension lower bound. It alone proves no completeness.
3. Free-table genericity does not imply economic genericity. The normalized
   scalar-covariate witness is valid, but analytic density still needs proof.
4. Likelihood rank is independent of initial state through nonzero column
   scales. Source-moment independence needs a separate argument or all three
   witnesses. The exact script checks all three.
5. Source Appendix A calls closed-form coefficient restrictions open, but
   this is not a guarantee of novelty against all other sources.

This is a mathematical review of a candidate argument. It is not the final
sentence-to-Lean statement audit required by the brief.

## Follow-up structural review

A separate read-only review examined the elementary arbitrary-period argument
in MANUSCRIPT.md: the single-block syzygy calculation, its homogeneous dimension
count, and the old-point interpolation correction when adding a block. It found
no substantive mathematical gap under the stated nonincidence conditions.
The following formalization obligations remain explicit:

- The interpolation correction needs quadratic local separators. The already
  checked quartics are too high-degree; new quadratic formulas have been written
  but have not yet compiled.
- Distinct projective points must be translated into the precise nonzero,
  nonassociated-line and coprimality facts used by the polynomial proof.
- Negative homogeneous degrees denote zero spaces. Natural-number truncated
  subtraction cannot silently represent this convention; low degrees need
  separate cases in the single-block dimension argument.

This follow-up supports the mathematical strategy, not a machine-checked
arbitrary-period claim.

# Proof dependencies

## Checked deterministic chain

```text
Weights.lean: actual Gamma/rpow weights and endpoint positivity
                    ↓
Adams.lean: concrete q,l,F and exact complex recurrence evaluation
            strong induction on polynomial highest coefficients
                    ↓
Exponent.lean: theta*gamma*h + V0*F, both trapezoid endpoints, drift
               degree 2*4^M and positive leading real coefficient
                    ↓
Tail.lean: coefficientwise real part → quadratic tail lower bound
           exp real-part bound → error against bounded comparison
           eventual positive lower bound → nonintegrability
                    ↓
Payoff.lean: max(exp(x)-1,0), exact full-line Fourier integral
                    ↓
Main.lean: every finite M; genuine payoff in the conclusion;
           dyadic mesh; infinite integral of all-level supremum;
           no integrable majorant after any fixed level; nonvacuity
                    ↓
AxiomAudit.lean: checked dependency-closure axiom lists
```

The proof uses only the pinned Mathlib dependencies. There is no external computed certificate or numerical lemma in this chain.

## Still-open financial chain

Rough-Heston process existence and moments → affine transform identity → identification of the bounded comparison with that model → contour admissibility → Fourier pricing inversion → derived nodal/time-integration rates → certified repair with stable frequency resolution → quadrature/tail/rounding estimates → actual option-price error.

The payoff integral at K=1/R=-2 is already proved. It does not supply the remaining stochastic or pricing links.

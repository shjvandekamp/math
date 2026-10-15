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

## Checked finite-band chain

```text
Weights + WeightProperties: nonnegative full rows, exact row masses
Adams + FiniteBand + Continuation: actual one-correction recurrence,
    predictor-before-corrector validation, weighted full-history induction
FractionalIntegral + RiccatiBounds + Volterra: actual singular integral,
    coefficient bounds, Holder continuity from the exact equation
ProductIntegration: actual kernel cell identities and derived defects
                         ↓
AdamsStability + NodalError + Convergence: local error and true consistency
WeightedKernel + WeightedRows: exponential full-history estimates
                         ↓
FixedHorizon + MeshConditions: fixed-maturity validated continuation,
    explicit positive threshold and one seed for all dyadic levels
ExponentError + TransformError: actual trapezoidal exponent, its error,
    exponential perturbation and affine-phase scaling
                         ↓
Approximation: one seed and constants uniform over the whole finite band
CoarseLevels: all levels of any original seed, at each fixed frequency
VolterraExistence + LocalExample: actual local solutions and nonvacuity
```

The general-coefficient approximation theorem assumes existence and a uniform bound for the exact solution family. It derives every numerical defect, row condition, mesh-existence claim and error estimate. The source's time weight and all-original-level conventions are covered by `CoarseLevels`, with constants that can depend on frequency. `ExactQuadrature` separately derives the source's pure exact-node trapezoid premise; `DeterministicResult` packages both source rates with strictly positive constants.

## Checked complementary identities and cutoff estimates

```text
FractionalIntegral + Beta/Gamma + convolution/Fubini
                         ↓
FractionalSemigroup: I^beta I^alpha = I^(alpha+beta)
Volterra + TransformBound: integral F(h) = I^(1-alpha)h(T),
    real-part barrier implies explicit exact-exponential bound
Payoff + FourierBounds: genuine call-factor decay, tail <= B/U,
    deterministic cutoff error <= U*E/2+B/U
LocalRegularity: little-Holder improvement from the actual integral
FractionalMaximum + InvariantRegion: maximum principle and first contact,
    concrete Re h<1 and finite-band norm bound, no regularity premise
GlobalVolterra + Cutoff + GlobalRiccati: global Lipschitz path contraction,
    cutoff removal, actual global concrete solution family
                         ↓
BandContinuity + DeterministicFourier: frequency continuity, actual global
    transform bound, integrability, cutoff/time error for genuine call
                         ↓
DeterministicResult: constructed family + source rates q=rT=alpha +
    D_alpha has infinite integral; constructed deterministic cutoff repair
```

For the concrete coefficients, every regularity, barrier, existence, bounded-comparison and integrability premise is discharged in this chain. The generic cutoff inequality retains explicit hypotheses; the concrete theorem proves them. These integrals have not been identified with option prices.

## Still-open financial chain

Rough-Heston process existence and moments → affine transform identity → identification of the deterministic exponential with that model → contour admissibility → Fourier pricing inversion → evaluated mesh/cutoff/quadrature/rounding certificates → actual option-price error.

The payoff integral at K=1/R=-2, finite-band numerical continuation and conservative derived rates are already proved. They do not supply the remaining stochastic or pricing links.

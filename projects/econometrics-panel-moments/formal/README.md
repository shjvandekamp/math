# Lean formalization

The foundation modules compile with Lean **4.34.1** and Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612` (release `v4.34.1`). The full dependency
revisions are pinned in `lake-manifest.json`.

The parameter `Q` in these modules counts **nonbaseline alternatives**. Thus the
paper's three-alternative, four-period model is `State 2`, `Path 2 4`; its path space
has 81 elements. Alternative zero has fixed-effect multiplier one. Time starts at
zero, and `r` is the fixed initial state before that time. `A t r q` orders the lag
state before the current state.

## Main theorems

- `PanelMoments.three_choice_four_period_generic_completeness` in
  `PanelMoments/EconomicGenericity.lean` proves independence and spanning of
  the 33 source moments and dimension 33 on an explicit joint economic region.
- `PanelMoments.StructuralCompleteness.three_choice_generic_moment_dimension`
  in `PanelMoments/StructuralCompleteness.lean` proves the dimension for every
  positive panel length on an explicit joint economic region.

Both regions are nonempty, open, and dense in their normalized scalar-covariate
parameter domains. Both main theorems passed clean source rebuilds, axiom
checks, and independent statement audits. See [../VERIFICATION.md](../VERIFICATION.md)
for the complete workflow and [../THEOREM.md](../THEOREM.md) for exact scope.
The arbitrary-period theorem does not prove general-period source-family
independence.

## Model foundations

- `Model.lean`: strictly positive normalized transitions and path likelihoods;
  transition probabilities and all path likelihoods each sum to one; the definition
  `IsMoment` requires zero expectation for every strictly positive normalized
  fixed-effect vector.
- `Polynomial.lean`: the minimal common denominator is the initial-state
  denominator at time zero times every lag-state denominator at subsequent times.
  Its evaluation is positive. Multiplication by it gives the explicit
  `clearedPathPoly`. `isMoment_iff_coefficient_kernel` proves both directions of
  the exact coefficient restriction, using the polynomial identity theorem on
  the strictly positive orthant.
- `Degree.lean`: cleared path numerators have total degree at most
  `1 + (Q + 1) * (T - 1)` for positive `T`. In the three-alternative, four-period
  case the bound is ten. Coefficients above the bound vanish, so only the bounded
  coefficient restrictions are needed.
- `Economic.lean`: the baseline common index is zero and the remaining indices
  are `gamma[q,r] + sum_k x[t,k] beta[q,k]`. The transition formula equals the
  normalized economic logit. Positive fixed-effect multipliers are exactly the
  exponentials of unrestricted additive fixed effects. The coefficient-kernel
  equivalence therefore applies to this actual economic specification.

These statements are model foundations. They do **not** prove a dimension of 33,
source-moment independence, completeness of a proposed family, or genericity of a
rank condition on the economic parameter space. In particular, substituting the
economic table into the kernel equivalence does not transfer a generic free-table
rank claim.

## Verification

With the pinned Lean toolchain on `PATH`:

```sh
./verify-foundations.sh
```

On this workspace, the toolchain can also be selected explicitly:

```sh
LEAN_BIN=/Volumes/2tb/math/.research-cache/toolchains/lean-4.34.1-darwin_aarch64/bin \
  ./verify-foundations.sh
```

For fresh dependency setup and verification of both complete main theorems,
follow [../VERIFICATION.md](../VERIFICATION.md). Use `lake resolve-deps` to
materialize the pinned manifest, rather than updating the dependency resolution.
The main entry point is `../verify.sh --clean`; the foundation-only script
above is retained as a narrower diagnostic.
On 15 October 2026, all four modules and their aggregate built successfully.
`FoundationCheck.lean` checked the axiom dependencies of the substantive
statements; its exact output is in `foundation-axioms.txt`. Every audited theorem
uses only `propext`, `Classical.choice`, and `Quot.sound`. No unproved declarations
or native computation oracle are present in these foundation sources.

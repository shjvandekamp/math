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

`SourceRelativeTimeJet.lean` proves the derivative of the actual homogeneous
kernel along a relative-time perturbation `(u,v) ↦ (u(1+τε),v(1+νε))`.
It also proves the cleared derivative identity, zero row sum, and the
derivative of the prefix-corrected append expression. These are derivative
identities; independence of the complete coalescent source-jet family remains open.
`SourceLocalJetAlgebra.lean` connects the exact two-branch kernel difference
to its derivative and proves the special jet's five-term expansion and
diagonal cancellation. Its fixed tail remains arbitrary; no residue or
rank claim is included. `SourceMixedPoleJet.lean` proves the actual
denominator-cleared numerator identity and its first derivative at a pair
of row-form zeros. The derivative allows an entrywise differentiable tail;
the actual ordered-kernel-product corollary proves this hypothesis from
nonzero row denominators in the tail. This does not assert a residue
asymptotic, nonvanishing, or rank result.

`SourceMixedPairDeterminant.lean` proves an explicit nonzero two-column
cleared derivative determinant at a common pair of row-form zeros. Its
actual-word corollary assumes nonzero coordinates, source entries, the
selected row minor, `ν−τ`, and the tail's row forms and block determinants.
Tail differentiability, row sums, and determinant nonvanishing are derived
from the actual ordered kernels.

`SourceMixedPairSeparation.lean` proves that the six off-diagonal special jets
are independent modulo the entire actual coalesced reduced source family.
It constructs their polynomial numerators with the exact common denominator,
proves that first pair coefficients annihilate every leading column, and uses
the two-column determinants to separate all six coefficients. Polynomial
injectivity transfers relations on positive coordinates to these observations.
The local geometric conditions remain explicit: neither their generic
existence nor old-source independence is assumed or proved. Full equation (24)
independence remains open in this formalization.

`SourceScalarPrependAlgebra.lean` treats the fixed common matrix
`G̃ = I + 11ᵀ` and the actual time curve `(u,v) = (1+ε,1+2ε)`.
On `∑ X_a = 0`, with nonzero coordinates, it proves the row forms,
`X K(0) = 4X`, and the explicit first derivative with `HasDerivAt`.
It also proves the SP6 and SP14 numerical determinants `1` and `−1/4`,
including their diagonal scaling consequences under explicit nonzero
endpoint factors. This module does not prove residue extraction,
generic existence, or an independence theorem.

`SourceWeightedPrependAlgebra.lean` extends the actual prepend identities to
`G̃ = diag(r) + 11ᵀ`. With `w_a = 1/r_a` and `S = 1 + ∑ w_a`, it proves
`X K(0) = SX` and the weighted first derivative, assuming nonzero `r_a`
and coordinates on `∑ X_a = 0`. It also proves the finite determinants
`det(I + w1ᵀ) = S`, `det(I − w1ᵀ/S) = 1/S` when `S ≠ 0`, and the
explicit three-quadratic coefficient determinant `−κ B₁₂ B₂₁ h k`.
These are kernel and matrix identities; residue extraction, generic
nonvanishing of the observation factors, and source independence are
not asserted by this module.

`SourceTerminalPrefixExtraction.lean` proves the actual terminal-kernel
identity `T_K K = diag(X)(I − K)`, the terminal coefficient shift, and
reconstruction of a constant prefix row from its own-line and two
coordinate-edge observations. The actual inverse corollaries retain explicit
matrix, coordinate, and row-form nonzero assumptions. These are finite
algebraic identities; residue extraction, ambient membership, generic
existence, and source-family rank are not asserted.

`SourceTimeScaling.lean` proves that multiplying every table column `b`
by a common factor `h_b` equals replacing coordinates by `h_b X_b` in the
actual row forms, kernels, and ordered products. Each empty, singleton,
and single-block vector gains the factor `1/h_a` for its first state `a`.
With positive factors, coordinate pullback and these nonzero column factors
preserve independence of both the actual source family and the reduced
family at each fixed length. The module does not assert that either family
is independent or prove determinant nonvanishing.

SourceBoundaryEndpointAlgebra.lean uses the actual weighted table and
kernel to cancel an output coordinate before restricting to a coordinate
edge. It proves the endpoint relation and the recovery determinant
S^2/product_k(S-w_k), positive for positive weights and independent of
the nonzero time factors. No residue interpolation or source-independence
claim is made.

SourceRepeatedPoleAlgebra.lean evaluates the existing polynomial-cleared
kernel at a row pole, proves its surviving rank-one formula, and computes
arbitrary positive-length powers and actual equal-block word products.
Nonvanishing retains explicit nonzero factors and the final-row
hypothesis. Parameter existence, residue extraction, and source rank
are not asserted.

SourceEndpointCoalescenceCoefficient.lean proves the identities and strictly
positive determinant of the endpoint calculation's displayed first coefficient
matrix, including A=4^m and B=3^m for every m>=1. Its ten declarations
do not identify that matrix with an actual source asymptotic coefficient;
residue extraction, limit control, and source independence remain separate.

SourceEndpointCoalescenceKernel.lean proves nine actual-kernel identities
on the closed active binary block, including the 3^m power formula and the
exceptional-row ratios used in the endpoint calculation. Its cancellation
ratio is explicitly defined; deriving that ratio from generic poles remains
a paper argument. SourceEndpointCoalescenceWitness.lean adds four theorems
evaluating the actual exceptional rows at z=(3/2,1,1) and proving the resulting
three-by-three determinant positive for every m>=1. This is a rational
extension witness: one last node lies on a coordinate edge and two coincide.
Perturbation to admissible generic geometry and source independence are not
formalized by these modules.

SourceBinaryTerminalAlgebra.lean proves eight identities and derivative
statements for the actual terminal factors (1,epsilon,tau). The missing
output column vanishes at zero; a fixed completed row's derivative contracts
to -X_1 f for canonical data (s_0,f,s_2). Only the fixed G is inverted.
Its determinant and all baseline row-form units are explicit hypotheses.
The scalar residue-kernel correspondence and rank criterion remain paper
arguments.

SourceWeakHermitePolynomial.lean verifies the cubic Hermite polynomial
identities used by the actual quotient calculation.
SourceInvariantTailAlgebra.lean proves the tail-weight identities,
endpoint factors, and the nonzero three-evaluation determinant.

SourceInvariantTailBaseData.lean and SourceInvariantTailBaseCertificate.lean
prove that the three displayed rational initialization matrices are
nonsingular, by integer column scaling and kernel-checked modular inverses.
The generator is ../exploration/generate_invariant_tail_lean.py.
SourceInvariantTailActualBase.lean separately derives the two-block
binary annihilation, retained heads, and four weak rational functions
from the displayed H/J formulas over the reals, with exact rational
constants. SourceInvariantTailWeakDerivative.lean differentiates the
actual homogeneous kernels and completed H/J rows.
SourceInvariantTailBaseDerivativeBridge.lean identifies the constant
Gamma combination's actual source derivative as minus (r-z) times
the four displayed weak functions. Its normalized derivative has the
same minus sign. Only the explicit row-form units, and r != z when
normalizing, are assumed. Complete source-family indexing and later
initialization matrices are not identified by this bridge.

SourceInvariantTailPolynomialExtension.lean proves injectivity of the
normalized polynomial extension by four evaluations.
SourceInvariantTailConcretePolynomials.lean supplies its actual displayed
polynomials and verifies the evaluation conditions.
SourceInvariantTailBoundedExtension.lean proves the degree bounds, equal
dimensions, linear equivalence, and unique decomposition.
SourceInvariantTailSchedule.lean discharges every nonzero-factor condition
from the explicit interval and distinctness assumptions, with
a=6/5, z=1/10, and the tail weights. Its final unique-decomposition
theorem has no assumed matrix rank or unspecified evaluation pivot.
SourceInvariantTailNormalization.lean checks the literal rational
transfer and all three new generators, including the third-column
replacement, against that polynomial model with explicit denominator
units. Reconstruction holds also at r=z; division by r(r-z) has the
additional nonzero assumptions.
The source-word identification, later finite initialization, and generic
specialization bridges remain separate obligations. These modules do not
assert an end-to-end all-length paired or equation-(24) theorem.

SourceRankOnePrepend.lean proves the actual empty/single-source
commutator identity, rank-one prepend collapse, and the first kernel
jet with the old factors fixed. The paper's residue-rank bounds do not
form part of this module.

SourceConfluentQuotientAlgebra.lean proves the corrected three-class
matrix determinant, its odd-row replacement determinant, the quotient
coordinate conversion determinant, and the nonzero coefficient bounds
for every natural length at least three. It does not identify that
replacement row as an actual derivative or prove source-space confluence.

SourceConfluentCubicAlgebra.lean identifies its rational K with the
actual homogeneous kernel, proves entrywise derivatives of K, U, V, S
and Y at x=1, and proves the ordinary observation determinant 397/2^37.
The same observations have determinant 3/256 on diag(X)(I-K), so they
do not annihilate the new empty-source columns. All 59 public declarations
passed a focused axiom audit. Time-Taylor identification, circulation
rank, and quotient rank are not asserted by this module.

The source-family verifier now derives its project module list from
the actual imports of SourceFamilyCheck.lean in dependency order.
The previous fixed list omitted newly added modules and could rely
on their cached outputs. Syntax and dependency-order checks passed, followed by the final
complete clean rebuild below.

The final source-family verifier passed a clean rebuild of all 66 project
modules and all 1,013 requested declaration audits on 16 October 2026.
Only propext, Classical.choice and Quot.sound occur. The serial run took
600.48 seconds, with maximum RSS 2,497,609,728 bytes, under the 2500 MiB
Lean cap. The only diagnostics were two existing style warnings in
BasisCertificate.lean and SourceAppendIdentities.lean. Evidence is saved in
[source-family-final-clean-build.log](source-family-final-clean-build.log),
[source-family-final-clean-timing.txt](source-family-final-clean-timing.txt),
and [source-family-axioms.txt](source-family-axioms.txt); the extended axiom
file is an identical current copy. This verifies the stated formal modules,
not the still-open full equation-(24) theorem or the unformalized paper bridges.

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

# Fixed-effect-free moments in three-choice dynamic logit

This project proves two results for dynamic multinomial logit with three
alternatives, unrestricted individual effects, and one scalar covariate.
Both main theorems are fully Lean checked, independently audited, and rebuilt
from clean project outputs.

- **Four periods:** the 33 explicitly indexed Dano–Honoré–Weidner source
  moments are linearly independent and span the entire moment space, for
  every initial outcome, on an explicit nonempty open dense joint economic
  parameter region in R^10.
- **Every T >= 1:** on an explicit nonempty open dense joint economic region
  in R^(T+6), the complete moment-space dimension is
  `3^T - choose(3T,2) + 6(T-1)`, for every initial outcome. The structural
  proof identifies the cleared-likelihood span with homogeneous polynomials
  vanishing at six projective points per additional period, then proves
  equality by interpolation and induction.

The arbitrary-period result determines the whole space's dimension; it does
not prove independence of the source paper's particular family for every T.
Genericity is joint in the normalized state-dependence coefficients, slopes,
and covariates, not on every fixed-covariate or fixed-slope slice. No
measure-zero exceptional-set or estimator-identification claim is made.

Later written proofs, not yet formalized, extend the exact count to any
number of choices and give an explicit basis for every T:
[GENERALQ_ALLT_PROOF.md](research/GENERALQ_ALLT_PROOF.md) and
[GENERALQ_PROOF.md](research/GENERALQ_PROOF.md).

The bounded prior-art audit found **no matching public proof as of
15 October 2026**. Priority and publication value remain provisional;
[NOVELTY.md](NOVELTY.md) records the source comparisons and access limits.

Read [THEOREM.md](THEOREM.md) for precise statements and domains,
[MANUSCRIPT.md](MANUSCRIPT.md) for the mathematical argument, and
[DEPENDENCIES.md](DEPENDENCIES.md) for the formal dependency map.
[STATUS.md](STATUS.md) records the confirmed results and
[next steps that are not completed](STATUS.md#next-steps--not-completed).
The [research roundup](RESEARCH_ROUNDUP.md) separates the completed
theorems, new paired-independence proof, explored routes and remaining work.
The original request is preserved in [BRIEF.txt](BRIEF.txt).

The next work is to test the combined verifier and dependency bootstrap in a
fresh environment, prove the particular source family's basis property for
arbitrary T, and refresh the novelty audit before seeking external review.
These are future tasks, not additional verified claims.

The equation-(24) continuation now has an independently audited
[invariant-tail proof](research/SOURCE24_INVARIANT_TAIL.md) of generic
paired boundary independence at every length. Its actual-source finite
initialization was independently reconstructed by exact rational arithmetic.
Lean checks the displayed initialization matrices and several polynomial
and scalar components, including actual two-block source derivatives.
A second audited [ordered-confluence proof](research/SOURCE24_CONFLUENT_QUOTIENT.md)
establishes nonvanishing of the actual three-class quotient coefficient.
The new paired theorem is not yet formalized end
to end. The remaining full-source condition is the retained-old Schur
determinant \(D_q+Z_T-Z_BC_B^{-1}C_T\), with all insertion and head
corrections retained.

The continuation also has Lean-checked source validity, index counts,
recursive lifts, exact ordered matrix-product images, positive homogeneous
representations and a conditional polynomial induction criterion. External
finite source checks at T=5,6 and residue checks through T=8 remain finite
evidence. The auxiliary binary parity theorem is fully Lean checked.
[STATUS.md](STATUS.md#stopped-continuation-equation-24-for-t--5) retains
the detailed progress and distinctions between these results.

## Verification

After installing the pinned dependencies as described in
[VERIFICATION.md](VERIFICATION.md), run from this directory:

```sh
LEAN_BIN=/path/to/lean-4.34.1/bin ./verify.sh --clean
```

This runs the finite and structural source verifiers sequentially. The finite
component and structural component each passed their clean rebuild; the
combined entry point sequences those same commands. Their logs, exact axiom
output, and independent statement audits are linked in VERIFICATION.md.
Only `propext`, `Classical.choice`, and `Quot.sound` appear in the audited
axiom dependencies. No proof holes, custom rank axioms, or native computation
oracle are used.

Lean 4.34.1, Mathlib and all transitive revisions are pinned under `formal/`.
The exact exploration uses Python's standard library. Every certificate used
by the two main Lean theorems is checked by Lean's kernel. New paper results
and external initialization calculations are labeled separately; they do
not silently extend the formal theorem statements. Dependency sources and
compiled caches are not vendored.

The full development history is in this repository's commit log.
Development used an isolated worktree under `/Volumes/2tb/math/.worktrees/`.
This repository snapshot is not a journal publication; no source authors have
been contacted.

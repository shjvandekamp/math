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

The bounded prior-art audit found **no matching public proof as of
15 October 2026**. Priority and publication value remain provisional;
[NOVELTY.md](NOVELTY.md) records the source comparisons and access limits.

Read [THEOREM.md](THEOREM.md) for precise statements and domains,
[MANUSCRIPT.md](MANUSCRIPT.md) for the mathematical argument, and
[DEPENDENCIES.md](DEPENDENCIES.md) for the formal dependency map.
[STATUS.md](STATUS.md) records the confirmed results and
[next steps that are not completed](STATUS.md#next-steps--not-completed).
The original request is preserved in [BRIEF.txt](BRIEF.txt).

The next work is to test the combined verifier and dependency bootstrap in a
fresh environment, prove the particular source family's basis property for
arbitrary T, and refresh the novelty audit before seeking external review.
These are future tasks, not additional verified claims.

The active equation-(24) continuation has Lean-checked general validity,
exact index counts and lift foundations, external exact full-rank checks at
T=5,6, and a quadratic-size residue reduction checked by exact computation
through T=8. The original conic witness
has an exact T5 residue failure; a perturbed economic witness passes the finite
checks. The all-T determinant proof remains open. See
[the continuation note](research/SOURCE24_INDUCTION.md) and
[the updated status](STATUS.md#active-continuation-equation-24-for-t--5).

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
The exact exploration uses Python's standard library. External calculations
supply discovery data; every certificate used by a theorem is checked by
Lean's kernel. Dependency sources and compiled caches are not vendored.

The GitHub branch is
[`research/econometrics-panel-moments-20261015-01a13f56`](https://github.com/shjvandekamp/math/tree/research/econometrics-panel-moments-20261015-01a13f56/projects/econometrics-panel-moments).
Development used an isolated worktree under `/Volumes/2tb/math/.worktrees/`.
This repository snapshot is not a journal publication; no source authors have
been contacted.

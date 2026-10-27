# Verification record

**PASS — 2026-10-15, exit status 0.** Both the published finite-architecture
obstruction and the same-panel compatibility theorem were checked in
one complete fresh local-source build: **27 modules, 39 distinct audited
declarations** (43 printed lists including duplicates). Every audited list
contains exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Reproduce

From `projects/vix-overlap-consistency`:

```sh
scripts/verify.sh
```

The recorded complete run was:

```sh
scripts/verify.sh > notes/extension-verification.log 2>&1
```

The saved output has trailing spaces removed; its final line is:

```text
PASS: 27 local modules freshly compiled; exit status 0.
```

The entry point checks both exact JSON certificates against their literal
Lean tables, checks compiler/dependency revisions and unchanged dependency
sources, rejects local proof placeholders/custom axioms/native computation
oracles, rebuilds every local source in the import closure, and checks every
printed transitive axiom list. Linter warnings are present; there are no
build errors. Python checks are not proof oracles: the certificate identities
and their financial implications are independently proved inside Lean.

The build reuses pinned upstream Mathlib artifacts and always recompiles the
local proof closure. It is not a from-source rebuild of the entire
Lean/Mathlib ecosystem. Missing dependencies and artifacts are restored from
the pinned manifest. The fresh network bootstrap was exercised successfully
by the published baseline's GitHub CI.

## Pinned versions

| Component | Pin |
|---|---|
| Lean | 4.34.1 |
| Lean compiler commit | `5045d0056413266e57c625dcd7c365b10e377c52` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Transitive packages | Exact revisions in `formal/lake-manifest.json` |

The local run used arm64-apple-darwin24.6.0. Set
`VIX_LEAN=/absolute/path/to/lean` if needed. The script also recognizes the
installed compiler under `/Volumes/2tb/math/.research-cache/toolchains`.
No BrownianMotion or formal-mathfin declaration is imported. Initial
retrieval needs network access; checking saved certificates needs only
Python's standard library. SciPy is used only for numerical discovery.

## Headline statements and axioms

`VixOverlap.financial_three_window_obstruction` remains the published
restricted impossibility theorem, including all proper-panel witnesses,
common bounds/budgets, full window log identities, frozen tests and margin.

`VixOverlap.Extension.financial_same_panel_compatibility` supplies an actual
full filtered law for every `0≤ε≤1` on a fixed 6592-state carrier, with the
same complete vanilla panel, original initial data and moment bound, unit
stock forwards and all three conditional-log identities.
`Extension.information_restriction_is_essential` explicitly pairs broader
existence with restricted impossibility for every `0≤ε<1/30`.

The complete log contains:

```text
'VixOverlap.financial_three_window_obstruction' depends on axioms: [propext, Classical.choice, Quot.sound]
'VixOverlap.Extension.financial_same_panel_compatibility' depends on axioms: [propext, Classical.choice, Quot.sound]
'VixOverlap.Extension.same_panel_compatible' depends on axioms: [propext, Classical.choice, Quot.sound]
'VixOverlap.Extension.information_restriction_is_essential' depends on axioms: [propext, Classical.choice, Quot.sound]
'VixOverlap.HiddenModel.model' depends on axioms: [propext, Classical.choice, Quot.sound]
'VixOverlap.HiddenQuotes.model_fitsPanel' depends on axioms: [propext, Classical.choice, Quot.sound]
'VixOverlap.Mixture.model' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All other audited declarations have the same three foundational axioms.
There is no `sorry`, `admit`, `sorryAx`, substantive new axiom, native
computation oracle, external solver assumption or assumed continuous
realization in either proof closure. Finite integer facts use ordinary
`decide`; algebraic proofs lift them to real probabilities. Logarithms and
square roots remain exact real expressions.

## Statement and library audit

Independent source reviews are recorded in `notes/statement-review.md` and
`notes/extension-review.md`. The extension review found no material gap in
the ordinary observations, quantifiers, full model constructor, null-history
handling, root mixture conditioning, common moment bound or interpretation.
Its wording clarification was incorporated: the broader class allows extra
fixing signals and finite latent states; the witness is not claimed to be
merely a coarsening of the original 4096-state model.

The headline returns `FiniteModel`, whose fields require positivity,
adaptation, every martingale row, diagonal log row and full tower row.
`Broad.Admissible` and `Broad.FitsPanel` contain restrictions and observed
prices, not an assumed existence result. Nonvacuity follows from the explicit
normalized positive witness. Pointwise signal identification uses proved
positive history masses. Mixture proofs multiply unnormalized branch rows,
including zero-weight branches at both endpoints.

The previously inspected Mathlib logarithm, square-root and factorization
results remain unchanged. The new finite conditioning proof partitions sums
into finite equivalence classes; it assumes no measure-theoretic realization
result. PROOF_MAP.md records every main implication. Novelty is a separate,
provisional assessment in NOVELTY.md.

## GitHub publication

The authorized original baseline was pushed and merged through
[PR #2](https://github.com/shjvandekamp/math/pull/2) at main commit
`bffaa68ca7b965162e6437d30f90881ce64bff15` on 2026-10-15.
Its [main-branch CI run](https://github.com/shjvandekamp/math/actions/runs/38745717506)
and [PR CI run](https://github.com/shjvandekamp/math/actions/runs/38743905081)
both passed. Each ran the complete baseline verifier: 19 local modules and
22 audited declarations. `notes/verification.log` preserves the fresh local
publication run. The compatibility extension is now published through
[PR #3](https://github.com/shjvandekamp/math/pull/3). Its first
[full 27-module Linux CI run](https://github.com/shjvandekamp/math/actions/runs/38753211263)
passed on commit `916a761`; the PR records checks for the final publication
head. Research on this project closed on 2026-10-15; no later exploratory
theorem is included.

CI pins checkout to `3d3c42e5aac5ba805825da76410c181273ba90b1`, installs the
Lean 4.34.1 Linux archive, and checks its official SHA-256
`47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4`.
The Ubuntu 24.04 image is maintained rather than bit-pinned; compiler and
dependency identities are checked independently. An initial bootstrap failure
was repaired by excluding compiler-supplied `Lean.*` modules from Mathlib
cache roots. The subsequent fresh-install CI passed; no theorem changed in
that repair.

## Resources and discovery

Local builds were serial, single-threaded and `nice 19`, with Lean's internal
allocation cap at 4096 MB. This cap is not a physical-memory measurement.
No other task's process was modified. Exact hidden-certificate checks cover
all 624 original rational equations and match all three 39-entry Lean data
vectors. Those checks support reproducibility; the main evidence is the
kernel-checked financial construction. Failed model-design approaches and
search details are preserved in THEOREM.md, `notes/model-audit.md` and
`notes/hidden-search.md`.

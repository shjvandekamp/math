# Research status

2026-10-15: the published finite-architecture obstruction and the published
same-panel compatibility extension are complete and kernel checked. The
same panel becomes compatible when hidden activity and fixing-time signals
are allowed. Mathematical novelty remains provisional.

Research on this project closed on 2026-10-15. No later exploratory claim is
included as a proved result.

## Published baseline

For every real `0≤ε<1/30`, the exact ordinary SPX/VIX panel has a compatible
law for every proper subpanel and none for all three windows in the declared
early-revealed activity class. The theorem includes full structural rows,
common root budgets and moment bounds, frozen local/pairwise tests, and the
positive separation margin `(1−30ε)/32`. It quantifies over all real
probability laws on all 64 schedules.

The baseline was pushed and merged in
[PR #2](https://github.com/shjvandekamp/math/pull/2) on 2026-10-15.
Main commit: `bffaa68ca7b965162e6437d30f90881ce64bff15`.
The [full main-branch Linux CI](https://github.com/shjvandekamp/math/actions/runs/38745717506)
passed after a fresh dependency bootstrap. The publication log remains in
`notes/verification.log` (19 modules, 22 audited declarations).

## Completed compatibility extension

For every real `0≤ε≤1`, `Extension.financial_same_panel_compatibility`
constructs a finite filtered model fitting exactly the same SPX and three VIX
call strips. The original stock-return kernel, root budgets, tenor and
moment bound are retained. Every martingale, diagonal and tower equation,
all window log-contract identities, all ordinary calls and unit stock
forwards are proved. `Extension.information_restriction_is_essential`
combines broader compatibility with the published restricted impossibility
for every original parameter `0≤ε<1/30`.

The zero-parameter witness has 39 positive schedule/signal entries with
integer weights over 1024 and 64 independent sign vectors, giving 2496 raw
states. A proved mixture with the uniform baseline uses a fixed 6592-state
carrier for the entire parameter family. The mixture branch is revealed at
event 1; the root remains trivial. Null histories and both endpoints are
handled without dividing by a branch probability.

The broader class permits additional finite signals and latent states. This
is not claimed to be a coarsening of the old filtration on its original
4096-state carrier. It is a compatible witness inside the broader contract
frozen in EXTENSION.md before search. The positive construction needs no
finite reduction of every possible broader law.

The complete `scripts/verify.sh` run passed with exit status 0 on 2026-10-15:
27 local modules freshly compiled; 39 distinct declarations audited (43
printed lists, including repeated module audits). Every list contains exactly
`propext`, `Classical.choice`, and `Quot.sound`. The complete output is
`notes/extension-verification.log`. No unresolved Lean lemma remains in
either headline theorem. The independent review found no material gap; its
scope wording clarification was incorporated in EXTENSION.md.

## Scope, novelty and unresolved questions

The same-panel extension is resolved by compatibility. The broader question
whether a different ordinary vanilla panel exhibits a three-window
obstruction beyond all pairwise checks in a less restrictive class remains
unresolved in this project. No general pairwise completeness, continuous-path
realization, executable arbitrage, global minimality or exchange-settlement
claim is made. Qualitative filtration sensitivity is already prior art.
No matching public resolution of this exact construction was found as of
2026-10-15, with the source-access limitations recorded in NOVELTY.md.

## Publication and reproduction

Worktree: `/Volumes/2tb/math/.worktrees/vix-overlap-consistency`.
The compatibility extension is published through
[PR #3](https://github.com/shjvandekamp/math/pull/3), branch
`research/vix-overlap-extension`. Its first
[full 27-module GitHub CI](https://github.com/shjvandekamp/math/actions/runs/38753211263)
passed. The unused exploration branch was removed after research stopped.
The primary checkout's unrelated files and other research worktrees were
preserved.

From this project directory, run `scripts/verify.sh`. The pinned toolchain,
manifest, proof map, exact tables, discovery scripts, manuscript, statement
audits and build logs are present.

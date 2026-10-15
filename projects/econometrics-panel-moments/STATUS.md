# Research status — 15 October 2026

**Confirmed:** the four-period source-basis theorem and the arbitrary-period
structural dimension theorem compile end to
end, pass axiom and independent compiled-statement audits, and have successful
clean source rebuilds. The broader arbitrary-period source-family conjecture
remains outside the proved claims. Novelty is supported by a bounded prior-art
audit, with no guarantee of priority.

Repository: `shjvandekamp/math`, research branch
`research/econometrics-panel-moments-20261015-01a13f56`, based on
`fe3e100fa673a64037771e42d95b7718379a29bd`. Other research worktrees and the
primary checkout are preserved. The GitHub snapshot contains the proved
results, saved validation evidence, and the uncompleted next steps below.
No journal submission or source-author contact has been made.

## Finite theorem

`PanelMoments.three_choice_four_period_generic_completeness` proves that the
33 specified DHW source moments form a basis of the actual fixed-effect-free
moment space, for every initial state, on an explicit nonempty open dense
subset of the joint normalized scalar-covariate economic parameter space R^10.

The successful clean verifier compiled 72 project modules, including all 39
scalar certificate chunks, the model-consistent witness and final assembly.
The saved output is `formal/finite-clean-build.log`; the axiom output is
`formal/main-axioms.txt`. The independent mapping from the compiled statement
to the source model passed in `reviews/FINITE_STATEMENT_AUDIT.md`.

## Structural theorem

`PanelMoments.StructuralCompleteness.three_choice_generic_moment_dimension`
proves, for every T>=1 and every initial outcome, on an explicit nonempty
open dense joint economic region in R^(T+6),

\[
\dim M_T=3^T-\binom{3T}{2}+6(T-1).
\]

The proof characterizes the cleared-likelihood span as the degree-(3T−2)
polynomials vanishing at six explicit projective points per additional
period. All cubic relations, interpolation, block induction, likelihood
correspondence, economic witness and analytic genericity are proved in Lean.
The natural-number formula is grouped with the positive correction before
subtraction, and follows from a proved additive identity.

The structural clean verifier compiled its entire 24-module project closure,
then checked the main declaration and eleven substantive dependencies.
It exited zero with “Serial structural source verification completed.”
Evidence is in `formal/structural-clean-build.log`,
`formal/structural-axioms.txt`, and `reviews/STRUCTURAL_STATEMENT_AUDIT.md`.
Both theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`.

## Scope and open questions

The arbitrary-period dimension formula does not establish independence of
the source's particular family for arbitrary T. An arbitrary-number-of-choices
extension, genericity on every fixed-covariate or fixed-slope slice, a
measure-zero exceptional-set theorem, and statistical identification or
estimator efficiency are not claimed. The finite and structural generic
regions are separate sufficient sets.

The bounded prior-art audit found no matching public proof through
15 October 2026. `NOVELTY.md` records the comparisons and inaccessible searches.
The structural argument, rather than the finite certificate alone, is the
proposed substantive research contribution.

## Next steps — not completed

These tasks are proposals for subsequent work. They are not prerequisites
silently assumed by either proved theorem, and no result below is claimed.

1. **Exercise the complete reproduction workflow in a fresh environment.**
   Materialize the pinned manifest, download dependencies, and run the combined
   `./verify.sh --clean` command in one invocation. Preserve the resulting log
   and environment details. Both component clean builds already passed, but
   the combined invocation and a fresh-machine dependency download have not
   been executed. See [VERIFICATION.md](VERIFICATION.md) for that distinction
   and the development host's resource limits.
2. **Prove the particular source-family basis for arbitrary panel length.**
   Formalize DHW equation (24)'s general-T indexing, validity and cardinality,
   then establish independence on a specified nonempty generic economic
   region. Combine that result with the proved moment-space dimension to
   obtain spanning. The current finite source-family proof is for T=4; the
   general-period dimension theorem alone does not supply independence.
3. **Refresh prior art and obtain external research review.**
   Check later versions and resolve the inaccessible searches recorded in
   [NOVELTY.md](NOVELTY.md) where possible. Seek separate mathematical and
   econometric review before making a publication-priority claim. The existing
   independent statement audits are internal agent reviews, not external
   peer review; no external review or author contact has been requested.
4. **Investigate broader geometric and economic statements.**
   Examine more than three choices, starting with a concrete small case;
   determine which specified fixed-covariate or fixed-slope slices admit a
   nonvanishing witness; and consider a formal measure-zero exceptional-set
   result or weaker sufficient conditions. Degenerate slices may fail, so
   joint genericity must not be promoted to a claim about every slice.
5. **Study statistical consequences separately.**
   Determine whether the moment family identifies the common parameters and
   how a chosen estimator uses the restrictions. Completeness and dimension
   by themselves do not prove identification, efficiency, or inference claims.

## Resource record

The final runs used one single-threaded compiler at a time, at `nice -n 19`,
with a 2500 MiB Lean cap under the host's 2.5 GiB aggregate allowance. Lake
exited before each compiler. All project verification jobs are finished.
No unrelated process was stopped or modified.

An earlier monolithic finite certificate attempt exceeded the host allowance
and was terminated. It was replaced by 39 independently cached scalar proof
chunks. The successful finite assembly's maximum RSS was 2,513,960,960 bytes,
with footprint 410,324,096 bytes; these are distinct operating-system
measurements. The host briefly paused the clean finite rebuild at a completed
module boundary and explicitly released that pause before it completed.

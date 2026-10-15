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

## Active continuation: equation (24) for T >= 5

The continuation is **in progress**. The accepted results below are unchanged;
independence of the particular equation-(24) family for every T is not yet
proved or Lean checked.

The exact source index audit includes footnote 8's restriction: for three
outcomes and j>=2 shared positions, the first j−1 shared positions must be
0,...,j−2 in zero-based notation. The correct counts are 162 at T=5 and 606
at T=6. Naively extending the old T4 generator without this restriction gives
too many rows.

New external exact computations in `exploration/general_source24.py` find
full row rank at a model-consistent perturbed witness with G[2,2]=17:
162 at T=5 (two primes) and 606 at T=6 (one prime), covering all initial
states by exact nonzero row rescaling. The unperturbed power-of-two witness
has smaller ranks modulo those primes. A separate rational calculation now
certifies rank 51 and three independent integer nullvectors for its T5
54-square residue matrix. This is an exceptional-witness failure, not a
generic counterexample. These new certificates are not Lean proofs and are
separate from the previously verified results.

The structural route splits the source family into three shorter-panel
indicator lifts and 3(T−2)(3T−8) new quotient classes. Its remaining matrix
has size 9(T−2)(T−3), instead of exponentially many path columns.
`exploration/source24_residue.py` matches the direct quotient ranks at
T=4,5,6 and finds full residue rank at T=7,8 for the perturbed witness.
It independently rechecks the saved T5 source minor. These are external
exact calculations, not an arbitrary-T nonvanishing proof.

The research argument and precise remaining nonvanishing problem are in
[research/SOURCE24_INDUCTION.md](research/SOURCE24_INDUCTION.md). General
permutation-moment validity, the exact canonical three-choice family and
indicator-lift validity/independence now compile in separate Lean modules.
The actual source index cardinality is also proved for every T>=3, including
its recurrence and the totals 162 and 606. The exact inherited-index bijection,
canonical order transport, and equality of source functions with shorter
indicator lifts are now proved. Every non-inherited index has explicit empty
or singleton coordinates. The actual conditional-tail expectation map has
the expected kernel, and Lean proves that shorter-family independence plus
independence of the new conditional images implies full source independence.
That last hypothesis remains unresolved. The joint first-state image is now
proved equivalent to the tail map by injective multiplication by the positive
first transition. Lean now identifies the actual source joint images with
normalized ordered transition-matrix products: the empty and singleton
cases have the prescribed effect factor, prefix transition, and delta-minus-
product form. The proofs use the actual canonical source orders and finite
Markov path sums. Lean also proves that the selected block comes first,
followed by the other blocks in ascending order, with the shared block
omitted in the singleton case. The homogeneous residue interpretation
remains to be formalized.

The empty-prefix columns now have an exact reversible reduction to
single-block columns. Lean proves span and independence equivalence, then
connects it to the actual new joint images using the exact index equivalence,
a common positive denominator and nonzero constant column factors. The
resulting source-induction theorem still explicitly assumes independence
of the reduced new columns.

The dedicated verifier rebuilt all 24 modules in this closure and checked
220 declarations; its axiom checks report only the three permitted foundational
axioms. Evidence is in
`formal/source-family-clean-build.log` and `formal/source-family-axioms.txt`,
with independent statement reviews in `reviews/SOURCE24_FOUNDATIONS_AUDIT.md`
and `reviews/SOURCE24_RECURSION_AUDIT.md`. These results do not establish
independence of the additional source rows.

Two further modules now connect the binary transfer functions to the actual
ordered stochastic matrices and restrict their rank theorem to positive
arguments. Their focused source checks and 34 additional axiom checks passed.
The extended aggregate checks 254 declarations; the reproducible closure now
contains 26 modules. The earlier 24-module clean build is preserved separately.

Further exact discovery separates identities from rank evidence. The
coalescent triangle and grid identities match direct rational series checks;
their nonzero curvature is not a full determinant. The tested constant-time
and normalized sparse witnesses give deficient modular evaluation matrices.
For the absorbing-state degeneration, a legitimate first-jet elimination
reaches full rank at n=2 but only 51 of 63 columns at n=3. The auxiliary
binary family now has a Lean proof of rank 2m for odd m and 2m−2 for even m.
It treats the actual move-first Q/R words, proves their relation to the prefix
defects, and establishes endpoint separation, paired-defect independence,
and the parity span identities over constant real coefficients. The theorem
assumes a nonempty coefficient list, rho different from zero and one, nonzero
entries, and adjacent distinctness. The actual matrix-product functions
q(P_i) and z*r(P_i) now have the same rank on z>0, assuming rho>0,
rho different from one, positive coefficients,
and adjacent distinctness. Lean proves positive-domain restriction injective
by polynomial uniqueness and uses a common nonzero determinant multiplier.
This remains an auxiliary binary result, not equation-(24) source independence.

The next paper argument restores the two missing directions at even length
by an asymmetric last-block perturbation. Its explicit two-dimensional
determinant is nonzero for every even length. Combined with the odd-length
leading calculation, this proves generic nonvanishing of the shared-new
polar half on the common-G, independent-time family. The independent internal
audit is [reviews/SOURCE24_POLAR_AUDIT.md](reviews/SOURCE24_POLAR_AUDIT.md).
The separate regular Schur half remains open, so this is not all-T source
independence. The polar theorem is not Lean formalized. Exact rational checks
and positive asymmetric finite first-jet witnesses are recorded in the
binary-polar-derivative and shared-new-polar-firstjet exploration files.
The exact block elimination now isolates a regular matrix H of size
9(T−3). Six finite asymmetric fixtures give full H ranks 18, 27, and 36
for T=5,6,7, with determinant factors checked; these are recorded in
`exploration/source24-schur-results.json`, not an all-T proof.

The regular quotient now has explicit constant-linear coordinates Delta.
They annihilate the transformed old single-block moments, give the identity
on the regular canonical columns, and reproduce the Schur matrix after a
nonzero diagonal row scaling. The derivation was independently reviewed;
`exploration/source24_regular_coordinates.py` checks these identities at
four finite fixtures. An attempted recovery of the old incidence coefficient
sums from axis restrictions and 3m matching normal derivatives fails: exact
stacked minors have sizes 54 and 75 at m=3,4, exceeding the observation
row counts 30 and 39. This rules out that proposed factorization on a generic
parameter set. It does not disprove source independence or richer methods.
The reproducible obstruction is in the source24-axis-jet-incidence files.

A precision-tracked Laurent computation follows the regular Schur matrix
as the new time factors tend to (epsilon, epsilon^3). Over the recorded prime,
the epsilon^-3 coefficient has ranks 6, 21, and 36 at m=2,3,4; the last
is full rank. Certified determinant valuations are -24, -75, and -108.
At m=3 the direct term contributes nothing at order -3, and the incoming
old-residue matrix already has rank 21; the subsequent old-block map preserves
that rank. An independently audited conditional paper argument proves the
leading-operator factorization and the sparse odd-length polar coefficients;
exact entrywise checks corroborate both formulas. The script and certificates
are the source24-regular-laurent exploration files.

The scalar incoming space now has an explicit residue basis and an exact
append-block recurrence. A support argument gives the uniform bound
`rank Z_-3 <= min(9m, 9*choose(m,2)-6m+12)`. At m=3 this is 21;
the saved nonzero minors establish generic characteristic-zero rank 21
for both the incoming and leading regular matrices. The entrywise valuation
bound, this rank bound and the saved determinant coefficients also prove
exact characteristic-zero determinant valuations -75 at the m=3 fixture
and -108 at m=4. The m=2 valuation -24 remains modular evidence only.

An audited degeneration proves six isolated incoming-column pivots for every
auxiliary m>=5. A second audited induction now proves generic full rank 9k+3
of the deletion-word residue family for every k>=4. It uses four exact
boundary pivots and five independent first-order kernel directions, with an
external nonzero 39-square modular minor as its k=4 base. Combined with the
exact deletion limit and the six isolated pivots, it proves generic incoming
rank 9m for every odd m>=5 under the stated polar hypotheses. This is a paper
proof with an external exact base certificate, not a Lean theorem; see
[the independent audit](reviews/SOURCE24_DELETION_AUDIT.md).

The deletion family has generic rank exactly 19 at k=3. Separate finite checks
find full ranks 39 and 48 at k=4,5 and confirm the fifth derivative direction
raises the shorter residue rank from 39 to 40. These reproducible certificates
are in the source24-deletion-word files. Direct checks also verify full incoming
and mapped ranks 45 at m=5 and 63 at m=7, including the actual old-source
equation OY=Z and polar hypotheses, in the source24-odd-incoming files.

The next unresolved step is proving that B0 O^-1 is injective on this incoming
image. The even-m regular calculation and the full regular determinant also
remain open. None of the new results establishes all-T source independence.

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
   The general-T indexing, validity and cardinality are now formalized.
   The exact recursive index bijection, source-lift equality, new-index
   parameterization, and conditional induction criterion are now proved.
   The joint/conditional map equivalence and actual ordered matrix-product
   formulas, including the explicit sorted-index forms, are now proved.
   Next formalize the homogeneous residue formulas and the audited polar theorem.
   The auxiliary binary independence and rank lemmas are now formalized.
   The actual new-image normalization and reversible single-block reduction
   are also proved. The actual binary matrix rank on the positive domain is
   now formalized. The paper deletion induction and odd incoming-rank theorem
   are audited; their external k=4 base certificate still needs Lean checking.
   Prove injectivity of the subsequent old-source map on the incoming image,
   and handle the even-length regular operator.
   The full Schur complement has size
   18(T−3); its shared-new polar half now has a paper nonvanishing proof,
   while the regular half after those pivots remains open. Prove that final
   nonvanishing on the common-G family and apply the scalar-covariate bridge.
   None of these open claims is assumed by a completed theorem. Combine
   independence with the proved moment-space dimension to obtain spanning. The completed source-basis theorem remains
   T=4; neither the dimension theorem nor the index count supplies independence.
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

The accepted main-theorem runs used one single-threaded compiler at a time, at `nice -n 19`,
with a 2500 MiB Lean cap under the host's 2.5 GiB aggregate allowance. Lake
exited before each compiler. Those verification jobs are finished.
No unrelated process was stopped or modified.

An earlier monolithic finite certificate attempt exceeded the host allowance
and was terminated. It was replaced by 39 independently cached scalar proof
chunks. The successful finite assembly's maximum RSS was 2,513,960,960 bytes,
with footprint 410,324,096 bytes; these are distinct operating-system
measurements. The host briefly paused the clean finite rebuild at a completed
module boundary and explicitly released that pause before it completed.

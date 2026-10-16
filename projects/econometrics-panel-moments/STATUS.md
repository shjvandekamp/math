# Research status — 16 October 2026

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

The latest paper result proves uniform full scalar/auxiliary rank of
actual zero-prefix source combinations for all m>=4. It uses an audited
induction and an external exact finite base. This auxiliary theorem
reduces the remaining source problem to a smaller actual determinant;
it does not establish the full equation-(24) family as a basis.

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
omitted in the singleton case. Lean now also proves the positive homogeneous kernel identity and the exact
X0 scaling of all source/reduced columns. An injective lift with section
X=(1,eta) makes homogeneous reduced-column independence equivalent to the
actual new-image premise, and gives the full conditional source-induction
step in these coordinates. Polynomial kernel matrices now clear the actual
ordered products and all reduced columns using one distinct-block denominator.
Positive evaluation and common-denominator scaling are injective, so Lean
also proves the equivalent polynomial-column induction criterion. The
algebraic residue interpretation remains to be formalized. The cleared
components are now also proved divisible by their output coordinates,
with exact polynomial quotient identities and no positivity assumption.

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
Two homogeneous-coordinate modules subsequently passed focused compilation
and 32 further axiom checks. The extended aggregate now checks 286 declarations
in a 28-module closure. Two further polynomial modules passed focused
compilation and add 29 axiom checks; the current extended aggregate checks
325 declarations in a 31-module closure, including the subsequent ten
output-coordinate divisibility results. The earlier 24-module clean build
is preserved separately; the extended aggregate reuses that compiled closure.

The new `SourceAppendIdentities` module now proves actual word appending,
whole-vector boundary annihilation, exact scalar splitting, and the
output-divided pole cancellation using the existing homogeneous and
cleared model kernels. Focused compilation and twelve further axiom
checks passed. The full-vector scalar-zero append factorization now
adds two further checked declarations. `SourceRelativeTimeJet` now proves
the actual relative-time kernel derivative, its cleared polynomial identity,
zero row sum, and the fixed-prefix append derivative. Its ten declarations
passed focused compilation and axiom checking. `SourceLocalJetAlgebra`
adds nine checked declarations for the exact two-branch collision
derivative, its five-term expansion, and diagonal cancellation after
clearing two row denominators. The new `SourceMixedPoleJet` adds eight
checked declarations: it relates the cleared numerator to the actual
special jet and proves its exact first derivative at a pair of row-form
zeros. The derivative depends on the tail value, with all tail derivatives
canceling. The actual ordered kernel tail satisfies the differentiability
hypothesis whenever its row denominators are nonzero at that point.
The updated aggregate checks 366 declarations in a 35-module compiled
closure, using only the permitted foundational axioms. This is a cached
aggregate check, not a new clean 35-module rebuild. The aggregate took
34.71 seconds with peak RSS 2,264,137,728 bytes under the serial memory cap.
Residue operators, matching-coordinate removability, asymptotic orders,
and the joint-rank induction remain paper arguments outside this module.

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

A further audited calculation shows that B0 has generic rank exactly one on
the 3m unmultiplied auxiliary source rows underlying the incoming formula.
It records the exact support and surviving coefficient, with four finite
fixtures checking the formulas. The actual incoming construction also selects
one component, multiplies by X_B/X_2 and changes the row direction. Those
operations are essential; the rank-one result gives no rank bound for the
actual incoming or mapped matrices.

The inverse-free residue-difference operator now gives a further audited
splitting. On the 3m seed residues it has matrix I−e gamma^T with
gamma^T e=0, proving seed independence and surjectivity onto the 3m
difference coordinates without old-source invertibility. The feedback map
on the full old moment-row space has rank 6m. The completion quotient
then separates an explicit contribution of at most one dimension from a
zero-sum lift with zero feedback. These statements do not prove the
required independence of the incoming family; see
[the residue-difference note](research/SOURCE24_RESIDUE_DIFFERENCES.md).
It also records three exact rational-zero relations in the k=3 deletion
family, consistent with the earlier finite residue-kernel report.

The next unresolved step is proving that B0 O^-1 is injective on this incoming
image. An independently audited completion-space construction now expresses this
map without the large old-source inverse, while preserving the actual
ordered-product incidence data; see
[the quotient formulation](research/SOURCE24_COMPLETION_QUOTIENT.md).
Its remaining condition is explicit complementarity of two spaces, not a
proved determinant. The binary part now has an explicit 6m-dimensional
quotient with actual polynomial annihilator conditions and a directly
constructed zero-sum incoming representative; see
[the binary quotient note](research/SOURCE24_BINARY_QUOTIENT.md). Its
incoming spanning condition remains open. Trying to recover incidence from all three axes also
fails: universal observation rank bounds are 72 and 90 at m=4,5, while
saved stacked minors with incidence have sizes 105 and 132.
The binary quotient note now also gives an audited explicit pair basis for
the sector whose component two is zero, of dimension 9*choose(m,2), and
a complete observation map for component two. Exact finite minors now
verify surjectivity on the annihilated source subspace at four and five
blocks; the three-block modular test is deficient. Uniform surjectivity
and independence in the resulting scalar quotient remain open.

The even physical constant correction now has an audited formula: one
2-by-2 kernel/cokernel solve plus a diagonal solve, under the established
polar hypotheses. It gives an explicit correction of rank at most six to
the sparse-shaped incoming family. Independent local Laurent polar solves
verify every constant coefficient at m=2 and m=4; the actual mapped ranks
are 6 and 36 there. See [the even correction note](research/SOURCE24_EVEN_CORRECTION.md).
All-length rank of this corrected even input and the full regular determinant
remain open. None of the new results establishes all-T source independence.

An audited [terminal peeling construction](research/SOURCE24_TERMINAL_PEELING.md)
now gives a recursive annihilator of the actual completion span, assuming
the final old-source matrix is invertible. It uses three cubic divisions
and boundary minors of size 18(m−1); it does not assume shorter incoming
complementarity. Its equivalent border determinant remains unproved.
Six exact finite fixtures verify append and actual seed-transport identities,
and the cubic identity is checked coefficientwise over the rationals.
The full recursive annihilator has not been implemented or Lean formalized.

The [append commutator](research/SOURCE24_APPEND_COMMUTATOR.md) cannot be
treated as a bounded-rank correction: an audited first-order degeneration
proves rank 3q in each coordinate sector for q>=2 and combined rank 9q
for odd q>=5, conditional on the audited incoming theorem. These are
pair-data ranks before quotienting by the completion span. Separately,
the [near-identity calculation](research/SOURCE24_NEAR_IDENTITY.md) shows
that two proposed leading blocks lose first-slot information. It leaves
higher coefficients and cross-block interactions open.

The [conic specialization](research/SOURCE24_CONIC.md) has particularly
simple pair points and divided-difference denominators. New finite exact
checks find full ranks 108 and 180 at four and five blocks, and rank 51
modulo the recorded prime in three distinct three-block examples. The
earlier exact rational rank-51 witness is preserved. Three independently
audited parameter identities now explain this defect throughout the
three-block conic family: two source combinations vanish as rational rows,
and the third equals an explicit nonzero single-block combination. Together
with the saved minor they establish generic residue rank 51, and generic
rank 52 for the 54 shared rational rows, on this special family. These are
paper results, not Lean theorems or counterexamples to general common-G
independence. A uniform proof from four blocks onward remains open.
An exact terminal calculation further shows that appending one admissible
block restores independence of these 54 interior residue columns. Their
three missing directions occupy three separate new-state sectors. The 54
raw completed three-block rows are already independent. Neither statement
settles the new boundary columns of the full enlarged family.

The audited [directed residue reduction](research/SOURCE24_DIRECTED_ELIMINATION.md)
turns the difference operator into outgoing-edge sums and removes 3m
explicit actual-source seed columns by an invertible triangular change.
The resulting square matrix has size 3m(3m−4); its invertibility is
equivalent to that of the old source matrix. This equivalence does not
settle the reduced rank question.

The audited [native-component construction](research/SOURCE24_NATIVE_COMPONENTS.md)
gives the exact component-two incoming quotient representative, a conditional
regular-limit criterion with saturation, and explicit terminal extraction.
The terminal formula extracts interior source coefficients, but the full
quotient has a further 18q−3 boundary directions, for m=q+1. Controlling
their quotient contribution remains open; the interior formula alone is
insufficient. Their extraction values and those of native seed components
are now explicit. A boundary-retaining exact sequence separates the
remaining quotient into dimensions 6+h and 6q−h, where h is the still
unresolved all-length rank of the boundary extraction matrix. Exact finite
minors give h=6q at q=2,3,4, with an independent q=3 fixture. Thus all
extraction outputs are already spanned by the boundary there, and the
remaining 6m quotient dimensions require the other part of the elimination.

A separate [raw completed-row route](research/SOURCE24_RAW_APPEND.md)
removes 6m+3 explicit row-sum constraints and proposes independence of the
new raw boundary modulo the entire appended old ambient space. Exact
finite minors establish this stronger sufficient condition at q=2,3,4;
the q=4 test required more effect points because row-sum relations limit
the number of independent evaluation rows. The
[explicit quotient](research/SOURCE24_RAW_QUOTIENT.md) now has 18q+9
coordinates, with its kernel proved exactly. A uniform 18-column
subfamily is generically independent modulo the appended ambient.
Direct exact quotient observations now certify the full boundary rank
at q=2,3,4,5,6. At q=4,5,6 the matching values add precisely 3,6,9
directions after the new-pole and axis observations. Separate matching
minors have rank 3q on the incoming unequal-state columns at every
tested fixture. A separate audited paper proof now establishes this
matching rank uniformly for every q>=2. Its coalesced matrix reduces
to explicit 3-by-6 tests, proved nonzero by exact power bounds. The
[fixed cyclic matching minor](research/SOURCE24_MATCHING_PIVOTS.md)
sharpens this to a specified 3q-column set, using a near-diagonal common-G
perturbation. Eliminating it together with six row-sum pivots leaves an
exact (15q+3)-by-(15q−6) reduced matrix whose full rank is still open.
Its specified square minor, omitting the nine new/old rows incident
to the last old block, is now certified nonzero at q=2,...,6; the exact
bordered determinant identity is checked at each fixture. This selects
a consistent candidate minor for a uniform proof without claiming one.
The audited [outgoing-pole reduction](research/SOURCE24_OUTGOING_POLE_REDUCTION.md)
now proves a uniform 9(q−1)-column pivot on exactly the retained
new/old rows. It combines a rational interpolation argument with explicit
binary-word determinants for both parities. After the same six row-sum
pivots, the specified determinant is equivalent to a square matrix of
size 9q+3 whose three diagonal state blocks are zero. All outgoing,
matching and axis corrections remain present. The reduced determinant
is certified nonzero at q=2,...,6, but its uniform nonvanishing remains
open. A further cycle reduction applies conditionally when three
off-diagonal blocks are invertible; this holds at the q=3,...,6 fixtures,
while each such block has rank 5 of 7 at the q=2 fixture.
The raw-quotient exploration files preserve the finite certificates.
The first old-time derivative also reaches the expected new-pole and
axis ranks in all five fixtures. A mixed construction retains the
coalesced matching matrix and applies only the new-pole/axis derivative
to the joint leading kernel. It reaches the full 18q quotient rank in
all five fixtures without using matching derivatives. This gives a
concrete uniform proof target; separate observation ranks are not added.
The joint leading rank is now proved uniformly to be 3q+15. Its kernel
splits into q−1 explicit 15-dimensional pieces through the path-incidence
matrix. The remaining task is injectivity of the actual first derivative
on their direct sum modulo the leading image. The formulas retain the
incoming prefix derivative and the cancellation of the highest old-pole
terms. These are paper reductions, not additional Lean theorems.
An audited moving-pole argument now bounds the order of consecutive-edge
differences by their distance from the endpoints. It also identifies
why the highest coefficients alone cannot separate interior edges.
Applying that filtration to the varying time directions and the local
matching constraints remains unfinished.
Exact coefficient profiles at q=3,4 expose cross-channel coupling:
the highest layers give zero gain in either channel alone but positive
gain with a shared leading correction. Old-pole coefficients leave
three directions, resolved by fixed new-axis residues at those fixtures.
A common increment U+3V also gives full mixed rank at q=3,4, supplying
a simpler finite witness for the next uniform attempt.
The audited [axis and matching recurrence](research/SOURCE24_AXIS_RECURSION.md)
reduces the axis identities to two coupled polynomial recurrences on
each axis and gives explicit matching equations at three fixed spectral
values. It retains the rational-pole conditions, endpoint terms and
the common leading correction. The forcing still depends on the
original source coefficients; eliminating it with the new-line
observations is unfinished.
The full 18q-column append proof and the further source-family
transversality remain open.

The binary quotient note also gives a parity-aware component-two reduction:
long-empty axis observations have rank 3m for odd m and 3m−2 for even m.
Odd lengths eliminate all axis annihilator coefficients; even lengths
leave two directions that first-slot differences must remove. The later
[actual-source axis spanning proof](research/SOURCE24_AXIS_SPANNING.md)
now removes those directions uniformly: T2(N) has rank 3m for all m>=3.
It uses two coprime quadratic differences followed by Laurent endpoint
elimination. The full pair-plus-axis component-two spanning remains open.
The new [actual-source normal restriction theorem](research/SOURCE24_NORMAL_RESTRICTIONS.md)
now gives every first normal coefficient and every second normal
coefficient from a subfamily with zero first coefficient, for all m>=4.
Its two append arguments preserve the prefix and the actual word order;
four independently reconstructed exact base minors are nonzero. After
axis elimination it supplies at least 5m−1 independent pair directions,
so the actual component-two image has dimension at least 8m−1.
This is an audited paper theorem with external finite certificates.
The remaining pair-weight space has dimension at most
9 choose(m,2)−(5m−1). Higher normal layers still require a compatible
lifting argument; the first two layers do not imply full spanning.
The remaining space is now identified exactly: S_m=p2(N)+F^3 S_m,
where F^3 consists of polynomials divisible by X0 cubed. A locally
proved ten-point cubic interpolation lemma gives the ambient normal-layer
dimensions through order m. Exact coupled kernel bases at m=4,5 isolate
the remaining 35- and 66-dimensional polynomial spaces and fill every
later layer at those fixtures. These finite profiles do not extend
the actual-source spanning theorem to general m.
The zero-prefix route now has an independently audited **uniform paper
proof of full scalar and auxiliary rank for every m>=4**. The theorem is
in [research/SOURCE24_JOINT_EXTENSION_PROOF.md](research/SOURCE24_JOINT_EXTENSION_PROOF.md).
For the actual zero-prefix source family Z_m it proves scalar rank
d_m=9 choose(m,2)+3m and rank 3m of the auxiliary-line restriction on
the same scalar kernel. It uses the external exact length-four joint
base (scalar 66, trace 12), the earlier audited boundary/body arguments,
and a new coupled three-pole extension. It is not Lean formalized and
is not an all-T equation-(24) independence theorem.

The induction keeps one full scalar projection, including normalized
inherited first-jet columns, and one projection onto the 3q old body
observations. Two new ordinary residues and one divided state-2 residue
annihilate every appended-old correction exactly. On three actual new
source columns, their corrected determinant begins
−36 epsilon^7 (Delta a−Delta b/v)^2 (Delta a−Delta b/(2v)),
which is generically nonzero. Fixing epsilon first and then taking the
auxiliary-line limit proves rank 3(q+1) for a single auxiliary map.
The scalar, body and final three directions retain the same source
coefficients; no independent ranks or simultaneous limits are added.
The primary researcher and two independent local audits checked this
argument, including the written proof.

The preceding construction and exact evidence remain in
[research/SOURCE24_ZERO_PREFIX_EXTENSION.md](research/SOURCE24_ZERO_PREFIX_EXTENSION.md).
The uniform 6q+3 boundary increment, 2q ordinary body pivots, and q
matching body pivots are its intermediate paper results. The matching
argument uses Laurent interpolation for q−1 directions and an additional
actual incoming column for the last one. Saved splitting certificates
at n=4,5,6 give scalar ranks 66,105,153. The body-limit and prescribed
projection certificates retain their original source coefficients,
including the failed C12+C22 selector and its successful repair.

A separate fully coupled finite endpoint test at q=4,5 gives
three-by-three Schur determinants 205708 and 135971 modulo 1,000,003,
and full auxiliary ranks 15 and 18. Its code and certificates are in
the source24-zero-prefix-endpoint-schur files. That test uses an older
third endpoint candidate; it corroborates the joint-rank target but is
not a numerical verification of the new three-pole leading formula.
The resulting length-seven scalar rank 210 and propagated bound
3m²+63 were intermediate paper consequences; the uniform joint theorem
now supersedes the lower bound.

The exact remaining source problem is smaller but still open.
[research/SOURCE24_SCALAR_KERNEL_REDUCTION.md](research/SOURCE24_SCALAR_KERNEL_REDUCTION.md)
uses full scalar rank to eliminate d_m actual source directions without
assuming the source matrix O_m invertible. It then uses the proved 3m
line-restriction pivots on those same coefficients. Writing
r=9 choose(m,2), the remaining criterion is an (r−3m)-square determinant
of actual scalar-zero polynomials divided by the auxiliary line.
Its sizes are 42,75,117 at m=4,5,6. The zero-prefix family and N alone
have too few coefficients to fill the remaining vector space; the
selected output-one/two source columns must be retained. Repeated
restriction or append does not automatically preserve this coefficient
kernel. Uniform nonvanishing of this residual matrix, and its Lean
formalization, are the next substantive obligations.

The divided residual polynomial space now has a generic ambient cubic
append recurrence at the required degree. An external exact three-block
quintic minor is 450004 modulo 1,000,003; together with the existing
block-extension theorem it gives the recurrence for every q>=3.
The source24-triple-quintic files record the certificate. Actual outgoing
sources realize its multipliers on long-empty difference seeds, but
realizing them on the full corrected source coefficient kernel remains
open. This identifies a concrete source-realization lemma rather than
another ambient dimension question.

An exact coefficient calculation now identifies why simple append
closure fails: the scalar/line coefficient kernel still maps onto the
entire 9q+3-dimensional append-prefix space. Thus its correction term
cannot generally be discarded. For q>=6 those constraints also leave
at least 3q(q−5)/2 arrival-index imbalance directions. These audited
obstructions concern formal coefficients and do not disprove source
independence or closure after the required corrections.

The boundary specialization now makes this obstruction exact: its
scalar observation is injective on the whole append-prefix space.
Copied append on the old residual coefficient kernel consequently has
boundary scalar rank 9q+3 and kernel precisely its zero-prefix part.
The latter has an injective normalized first jet on actual old rows
before the new scalar/line corrections. An adapted scalar section now
preserves exactly its old zero-prefix source kernel: a common complement
to two separate trace kernels prevents the trace pivots from erasing
the old joint kernel, and old double residues survive the ordinary
scalar correction. This is audited at G* with generic old times;
injectivity there still needs old independence at that same slice.
Preservation through the subsequent line correction remains open.
See (SK32)--(SK38); this does not supply residual independence.

A stronger audited result now fills the entire new scalar map using
only copied old full source columns, without assuming their independence.
The boundary prefix image intersects the inherited old scalar image in
exactly 3q dimensions; inherited trace jets supply the remaining 3q
directions. Scalar correction can therefore leave all new-pole tests
unchanged. Under an explicit shorter-length independence premise, the
remaining problem is an exact 9q-square determinant in a quotient of
the old scalar-zero polynomial space. This recasts the existing regular
Schur gap with all actual corrections retained; its nonvanishing is
still open. See (SK22)--(SK30) in the scalar-kernel reduction note.

Local ambient prefix recovery now gives explicit quotient coordinates.
Under the shorter-source independence premise, its actual source-graph
condition is a (9q+3)-by-r_q matrix with only five new-time monomials:
1,u,u²,v,uv. Its kernel is exactly the inherited scalar-zero image.
The boundary columns must still be proved transverse to that kernel;
the small polynomial degree alone does not prove this. See
`research/SOURCE24_PREFIX_PENCIL.md` for the audited formulas and
the necessary generic geometry.

The same local recovery extends to the entire transverse kernel:
(R,I)↦R K_n+I(I−K_n) is an ambient isomorphism. Under shorter-source
independence its source-graph defect has kernel exactly the copied-old
span. The three new local E rows map to the three constant prefix
coordinates. Hence, after only the shared-new polar elimination, the
remaining criterion is a 9q-square determinant of old-pole prefix
coefficients. This removes the scalar right inverse and the arbitrary
three-column quotient from the target, while retaining the actual
old source graph. Its nonvanishing is unproved; see (PP14)--(PP20).
A sparse source expansion now computes the pre-transport seed prefixes
explicitly: the polar-corrected old seeds have a block-diagonal old-pole
prefix matrix with determinant ±det(A_n)^(3q). The subsequent scalar
multiplier and inverse-append transport still change the old row, so
this does not prove the required defect determinant. Formula (PP25)
records that precise remaining transport, including its local-prefix
subtraction; see (PP21)--(PP25).

For each fixed new state b, the ambient transport now has a uniform
isomorphism theorem. The old rows whose multiplied new/old transverse
residues vanish form a complement D_b to the old E rows. After inverse
append, their old cross-pair residues are multiplied by explicit invertible
two-dimensional blocks, with determinant f_b(P)^2/det(K_n(P)). Thus
D_b maps isomorphically to the old ambient space modulo E. Polar
subtraction gives the equivalent quotient by the cycle rows. The 3q
transported seed rows for each fixed b stay independent modulo E.
This is audited paper algebra, not a Lean rank theorem or a proof
about the full 9q-column source-prefix matrix. The recovered prefix
has one exactly zero component after changing basis by A_n^{-1}.
The resulting tail identity and diagonal-sector coefficient law retain
the actual source completion and the polar correction; they isolate,
but do not settle, the remaining transversality. Polar subtraction also
identifies D_b modulo the corrected old zero-prefix sector with the
9q old-pole prefix coordinates; the transported zero-prefix sector may
depend on b. See (PP26)--(PP36).

The last-time coalescence alternative now has an audited inherited
rank result. When A_n=A_q, the ambient append map has a three-dimensional
kernel, but it meets the actual old source graph trivially. Copied-old
sources therefore stay independent under the shorter-length premise.
Exact ordered collisions leave only nine potentially new leading pair
rows; three diagonal ones are generically independent modulo the whole
ambient append image. The other six and the derivative directions
remain separate obligations. See
`research/SOURCE24_LAST_TIME_COALESCENCE.md`.
The exact relative-(1,2) first-jet tests are now full for q=4 and q=5:
their ranks are 195 and 288, with leading minor coefficients 23466 and
597175 modulo 1000003, at epsilon orders 66 and 84. The earlier u-only
q=4 test has sampled rank 193. These are external finite certificates;
uniform nonvanishing of the actual derivative block remains open.
The right logarithmic derivative now gives three explicit transverse
squared-pole blocks, each with 3(q−1) first-new columns. A Fourier/cycle
specialization reduces them to fixed-terminal deletion functions, but
the two-block deletion family has an exact constant-coefficient relation.
These observations neither give independence at longer lengths nor
eliminate the nine surviving leading rows; see (LC11)--(LC16).
Exact cyclic fixtures have full deletion ranks 9, 12, and 15 at
m=3,4,5 for all three states, while the separate two-block relation
gives rank exactly 5 there. A different local argument now proves a
uniform six-dimensional jet gain modulo the entire leading base:
the six off-diagonal special jets have invertible mixed third-order
pole blocks at the three same-block intersections. This requires
generic geometry and distinct relative weights, but no old-source
independence. With that premise it raises the established total
first-jet lower bound to N_q+9. The remaining jets require the actual
six-pivot corrections; their uncorrected ranks cannot be added.
See (LC17)--(LC18); this new uniform result is an audited paper proof.
The matching-point extension now proves all twelve local jets independent
modulo the entire base: three E derivatives and three diagonal special
derivatives add six further pivots. Their matching determinant is
τ²ν²(τ−ν)² r_0³ r_1 s_1³ s_2, and the full observation matrix is
block triangular with the previous six-pivot block. Under shorter-source
independence the lower bound is therefore N_q+15. The exact projection
retains every correction and leaves six leading off-diagonal W columns
and 18(q−1) corrected incoming/shared jets modulo C and the three
diagonal W: a specified 18q−12-column open rank problem.
A separate common-G residue induction proves vector deletion independence
for every number of earlier blocks; it does not imply scalar projection
or corrected quotient independence. See (LC19)--(LC25).
Two independent relative directions nevertheless recover that vector
family through the stacked incoming transverse observations. Each
direction loses at most twelve dimensions on quotienting by the
leading base and local jets, because the three E jets are invisible
to this observation. The resulting audited one-direction bound is
rank[B,D'] ≥ N_q+3+max(12,ceil(9(q−1)/2)) under shorter-source
independence. It gives N_q+17 at q=4 and N_q+21 at q=5, with all
correction losses retained. This is not full rank or a regular-pencil
proof; see (LC26)--(LC29).
For each leading off-diagonal survivor, an audited ambient preimage
now needs only one scalar prefix interpolation, in the third state
direction. The six leading-rank obligations are exactly a 9q-by-6
matrix of old-pole source-graph defects; its columns are independent
of the coalescent constant-prefix ambiguity. This smaller criterion
still requires the actual old source expansion and is not a proof
of full leading rank. See (LC30)--(LC32).
The exact leading-prefix recovery now has q=4 and q=5 witnesses.
At each time separately, the six pole rows with initial state 0 or 1
and all three outputs already distinguish the six columns. Triangular
153-point and 210-point interpolation grids certify the recovered
preimage identities over the finite-field rational-function field.
All source expansions are dense, so a sparse expansion shortcut fails.
An all-q formula for these six-row minors remains open.
A state-relabeling argument also strengthens the growing jet bound:
it holds for every fixed real direction with distinct weights, and
fixed direction (1,3) gives gain max(12,3ceil(3(q−1)/2)) over B.
With shorter-source independence this is N_q+18 at q=4 and N_q+21
at q=5. It is a generic independent-time-factor statement, not a
fixed-curve or full-rank theorem. The extended stripping lemma and
exact scalar deletion recurrence identify further correction terms
that still need control; see (LC33)--(LC37).

An actual ordered-path factorization now proves that the component-two
rank on N is at most 3^m. At m=3, together with the saved nonzero minor,
this gives generic rank exactly 27 and explains the nine-dimensional
deficiency. Its cleared cubic products provide a new route to investigate
larger lengths; their actual N coefficient combinations still matter.

The [pure-path polynomial induction](research/SOURCE24_PATH_SPAN.md) now
proves that all normalized path products span the entire component-two
ambient space generically for each m>=4. It combines an audited correction
argument with external exact 12-by-12 interpolation and 67-by-67 base
minors. This auxiliary theorem still leaves the restriction to the actual
N combinations open. The append identities retain their coupled
components and prefix corrections explicitly.
The new `PureCubicProducts` Lean module proves the conditional append step
and finite-horizon induction for the actual degree-3m products. Its
four-block base and lower-degree interpolation are explicit premises;
their external certificates and paper proof are not silently treated as
Lean proofs. Focused compilation and twelve foundational-axiom checks
passed. The existing 325-declaration source-family aggregate is unchanged.

The audited [conic transverse reduction](research/SOURCE24_CONIC_TRANSVERSE.md)
isolates a uniform 9n−6 pivot block. The binary parity theorem raises the
leading outgoing rank to 9n for odd n. The independently audited
[even-length first correction](research/SOURCE24_CONIC_EVEN_JET.md) now
restores all six missing directions for every even n. Thus the outgoing
transverse block is generically full rank at every length. The proof
retains state-zero pivots and uses a positive common-alpha conic witness;
it is a paper result, not Lean formalized. Exact dual-number checks at
n=2,3,4,6 corroborate the normalization. The audited
[regular leading-operator reduction](research/SOURCE24_CONIC_REGULAR_LEADING.md)
now cancels both departure and final factors and identifies the scaled
Schur limit as U_n O_n^{-1} D_n Z_0, retaining both old-node corrections.
An independently reconstructed exact certificate makes its determinant
nonzero at n=5. With the asymptotic proof, this gives generic conic O6
nonvanishing for sufficiently small positive appended times. It is an
auxiliary pair-source result with an external finite certificate, not
an all-length or full source-family theorem. Uniform nonvanishing of
the leading determinant remains open; the singular conic O3 also
requires a separate base step.
The audited [source-space compression](research/SOURCE24_CONIC_SOURCE_COMPRESSION.md)
expresses its three new-state sectors through one actual-source seed.
An explicit n(5n−8)-dimensional subspace of ker U reduces the old
inverse from size 9n(n−1) to n(4n−1), conditional on O being
invertible. The sparse seed has a single terminal defect under U;
the even correction is retained as a six-column border. These exact
identities leave the transformed-seed determinant unproved.
That singular step now has an exact 27-square criterion using its
51-dimensional old complement and three explicit longitudinal kernel
pivots. A separate suffix lemma shows that two appended blocks recover
the full rational-row rank of any old interior subfamily through pair
residues. Both statements preserve the incoming cross-coupling; neither
proves the new boundary rank. A second audited transverse argument
also proves the even correction for any fixed admissible binary
parameters when alpha0/alpha1 is sufficiently small and positive.

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
   The positive homogeneous representation, common polynomial clearing, and
   equivalent conditional polynomial induction criterion are now proved.
   Next formalize the algebraic residue formulas and audited polar theorem.
   The auxiliary binary independence and rank lemmas are now formalized.
   The actual new-image normalization and reversible single-block reduction
   are also proved. The actual binary matrix rank on the positive domain is
   now formalized. The paper deletion induction and odd incoming-rank theorem
   are audited; their external k=4 base certificate still needs Lean checking.
   Prove injectivity of the subsequent old-source map on the incoming image,
   and prove the remaining rank statements for the regular operator.
   The conic outgoing transverse block now has an audited paper proof for
   both parities. Its regular/longitudinal Schur block now has an audited
   leading-operator formula and a finite five-to-six-block witness;
   prove uniform nonvanishing of U_n O_n^{-1} D_n Z_0 with both old-node
   corrections retained. Its exact source-space compression now reduces
   the old inverse and identifies a common seed for all three sectors;
   prove transversality of its coordinate-transformed copies, keeping
   the even six-column border. Formalizing the transverse proof
   is also unfinished. The raw append alternative has an exact ambient
   quotient, a uniform 18-column subfamily and a uniform rank-3q
   matching map with a fixed cyclic minor. The specified minor of its
   (15q+3)-by-(15q−6) reduced matrix now has a uniform outgoing-pole
   pivot. Prove nonvanishing of the remaining (9q+3)-square matrix with
   zero diagonal state blocks, retaining the omitted-old-block pole
   contributions to its axis observations. Alternatively, prove that the first
   derivative is injective on the q−1 local 15-dimensional pieces of
   the joint leading kernel. The axis/matching recurrence and the
   common-increment finite witnesses narrow that second target;
   the coupled new-line equations must still be resolved.
   Both targets and subsequent source
   transversality remain open.
   The conditional terminal annihilator supplies explicit boundary rows;
   prove their pairing with the incoming columns is nonsingular while
   retaining the full old-node commutator. The explicit binary quotient
   still requires independence of its specific incoming classes. Its
   earlier normal-layer approach is now an alternative description:
   the zero-prefix theorem supplies uniform full scalar
   and auxiliary rank by an audited joint induction for m>=4, using
   an external exact length-four base. Formalize that base, the boundary
   and body proofs, the three-pole correction and the ordered-limit
   argument. Its source-independent scalar-kernel reduction leaves an
   (9 choose(m,2)−3m)-square actual polynomial determinant. Prove this
   determinant nonzero, retaining the selected output-one/two columns
   and the same scalar/line corrections. A corrected-append transport
   or a further restriction theorem on the existing coefficient kernel
   would be concrete next lemmas. Neither is yet established.
   The full Schur complement has size
   18(T−3); its shared-new polar half now has a paper nonvanishing proof,
   while the regular half after those pivots remains open. Prove that final
   nonvanishing on the common-G family. The prefix-recovery version
   (PP20) now expresses it as the 9q-square old-pole coefficient matrix
   of the actual source-graph defect after polar elimination, with no
   scalar right inverse. Compute its leading boundary term or prove
   transversality using the actual old source graph. The fixed-state
   ambient transport is now an isomorphism modulo the old E rows by
   (PP26)--(PP30), but its three state sectors still need a joint
   source-prefix argument. Neither that isomorphism nor the five-term
   pencil settles the determinant. Then apply the scalar-covariate bridge.
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

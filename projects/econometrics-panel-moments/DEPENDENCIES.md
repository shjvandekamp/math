# Lemma and dependency map

All finite and structural modules below compile and pass their integrated
axiom and independent statement audits. Clean source rebuild results are
recorded in VERIFICATION.md.

| Obligation | Depends on | Status |
|---|---|---|
| Transition probabilities and finite path expectation | Positive index table and effects | Lean checked: Model |
| Positive denominator clearing and exact polynomial kernel | Polynomial identity on the positive orthant | Lean checked: Polynomial, Degree, ModelAnalytic |
| Normalized economic model and nonzero analytic witness principle | Exponential index map and analytic identity theorem | Lean checked: Economic, Genericity |
| Source 33-row indexing | DHW equation (24), footnote 7, finite bijection | Lean checked: SourceMoments, WitnessCore; independently audited |
| Universal validity of source moments | Equal transformed-chain prefix marginals | Lean checked: SourceMoments, for every positive table |
| Fixed 48-evaluation minor nonzero | Primitive cleared formulas and inverse modulo 11 | Lean checked: WitnessEvaluation and all 12 chunks |
| Fixed 33-source minor nonzero, all initial states | Primitive source numerators and inverse modulo 11 | Lean checked: WitnessSource and all 27 chunks |
| Source basis from the primitive minors | Universal validity and rank-nullity | Lean checked: FiniteCompleteness |
| Explicit nonempty open dense R^10 economic region and finite main theorem | Analytic determinant product and certified economic witness | Lean checked: EconomicGenericity |
| Fixed homogeneous degree dimension and finite interpolation | Monomial count and explicit separators | Lean checked: HomogeneousInterpolation |
| Local and global quadratic separation | Conic geometry and products of other blocks’ lines | Lean checked: Geometry, QuadraticSeparators, GlobalInterpolation, GeneralGeometry |
| Normalized-line primality and homogeneous coordinate relations | Triangular substitution and coordinate ideal | Lean checked: LinearFormAlgebra, CoordinateSyzygies |
| One-block cubic range equals the six-point vanishing space | Relation-kernel equivalence and rank-nullity | Lean checked: CubicRelations, CubicIdeal |
| Correcting cubic coefficients at old points | Pointwise coordinate syzygies and interpolation | Lean checked: PointSyzygies, BlockExtension |
| Arbitrary-block product span equals the vanishing space | One-block equality and correction induction | Lean checked: CubicProducts |
| Actual likelihood kernel and range equal the structural spaces | Homogeneous dehomogenization and positive path weights | Lean checked: HomogeneousEvaluation, HomogeneousLikelihood, StructuralMoments |
| Explicit generic economic region for every T | Conic witness, polynomial nonvanishing factors and analyticity | Lean checked: EconomicFamily, GeneralConicWitness, StructuralGenericity |
| Arbitrary-T actual moment dimension | Structural span theorem and economic region | Lean checked: StructuralCompleteness; StructuralCheck axiom audit passed |
| General permutation moments and exact equation-(24) family validity | Actual transformed-chain marginal identities and canonical sorted orders | Lean checked: PermutationMoments, SourceFamily |
| Indicator lifts preserve validity and independence | Conditioning on the first outcome and disjoint supports | Lean checked: MomentLifts |
| Exact canonical index count for every T>=3 | Forced-prefix shared-set classification and finite counting | Lean checked: SourceCounting; count alone does not establish independence |
| Actual source-index and moment-function recursion | Shared-slot insertion, canonical order transport, and first-scale cancellation | Lean checked: PermutationLifts, SourceRecursion, SourceLifts |
| Exact empty/singleton coordinates for every new index | Omitted-zero shared-set classification and explicit inverse constructors | Lean checked: SourceNewIndices |
| Conditional induction from shorter families and new images | Actual tail-expectation kernel and index partition | Lean checked: SourceConditional; new-image independence is an explicit unresolved hypothesis |
| Joint and conditional image independence agree | Positive first-transition multiplier is injective | Lean checked: SourceJointImage |
| Auxiliary binary scalar parity and baseline remainders | Actual prefix identities and constant-real span induction | Lean checked: BinaryTransferAlgebra, BinaryTransferSpan |
| Auxiliary binary rank for the actual move-first words | Polynomial endpoint separation, paired-defect independence, actual word identities and parity spans | Lean checked: BinaryTransferEndpoints, BinaryTransferIndependence, BinaryTransferRank |
| Shared-new polar nonvanishing at every length | Binary rank and explicit even-kernel perturbation | Paper proof and internal audit; not Lean checked; regular Schur half remains open |
| Explicit regular quotient coordinates and Schur equivalence | Divided old-line residues, coordinate-edge evaluations and transformed single-block correction | Paper proof and internal audit; finite exact entrywise checks; no source determinant assertion |
| Quotient reduction to a quadratic-size residue determinant | Conditional sums, line residues and local-pair coordinates | Mathematical derivation in research/SOURCE24_INDUCTION.md; not Lean checked |
| Arbitrary-T independence of the source’s particular family | A separate argument beyond dimension | Open; not claimed by the structural theorem |

Neither accepted main theorem assumes a missing rank or independence result.
The continuation's induction criterion is explicitly conditional and is not
an arbitrary-period source-basis theorem. The external integer coefficient certificates remain discovery
evidence; the finite Lean theorem uses independently checked evaluation
certificates instead.

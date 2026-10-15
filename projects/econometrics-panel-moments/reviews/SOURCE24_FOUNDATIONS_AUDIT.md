# General source-family foundations: independent statement audit

Date: 15 October 2026.

Result: PASS for the stated validity and lift foundations. This is not an
independence or completeness certificate for the general source family.

## Evidence inspected

- `formal/PanelMoments/PermutationMoments.lean`
- `formal/PanelMoments/SourceFamily.lean`
- `formal/PanelMoments/MomentLifts.lean`
- Their three `.lake/*-axioms.txt` outputs
- The actual `State`, `Path`, `PositiveEffects`, and `IsMoment` definitions
- Previously inspected DHW equation (24), footnotes 7–8, and equation (16)

No additional compilation was run. The independent read-only reviewer
returned this text; the primary agent saved it without changing its findings.

## Statement-to-model correspondence

`State 2 = Fin 3`, so the canonical family has exactly three alternatives.
The horizon is `N + 1`. `IsMoment` requires zero expectation over every
positive vector of the two nonbaseline fixed-effect multipliers, with
baseline multiplier normalized to one. This is the actual model likelihood,
not a surrogate polynomial predicate.

`SourceFamily.sourceMoment_isMoment` quantifies over every positive table,
every initial outcome, and every canonical index. It assumes neither rank,
independence, genericity, nor the desired conclusion.

The transformed chain starts with table zero and, after generating slot s,
uses table s+1. The generation order fixes the final slot. The proved
`scaleRatio_mul_likelihood` identity therefore matches equation (16):
the fixed-effect product and denominator product cancel under reordering.
`originalScale` is the original path's product of primitive table entries;
its strict positivity is proved from `PositiveTable`.

## Exact canonical family

`SharedSet N` requires `card + 2 ≤ N`, equivalent to j ≤ T−3, and contains
every slot below `card−1`. For a sorted shared set, this is exactly the
three-choice footnote-8 restriction: its first j−1 slots are 0,...,j−2.

`firstSlot` is the minimum complementary slot. `SecondSlot` selects any
other complementary slot. `SourceIndex` supplies q₀ and all shared labels.

`coreList` orders the shared slots increasingly, then the first divergent
slot, then the remaining slots increasingly, then the second divergent
slot. `appendLast` appends the final observation. Swapping the divergent
slots produces the second order. This implements footnote 7 literally.
Permutation, common-prefix, and actual divergence properties are proved.

`sharedWeight` and the two divergent indicators match equation (24).
The explicit numerator is proved equal to the general permutation
numerator; dividing by the common positive original path scale gives the
actual moment. The ring-homomorphism theorem transports the polynomial
numerator only; it makes no unsupported assertion about division in a
finite field.

## First-state lifts

`firstStateLift a m` is the indicator of the first observed outcome a
times m on the remaining path. Its validity theorem uses the shifted
table and initial outcome a for the shorter panel, and permits every
initial outcome r in the longer panel.

Injectivity is proved by evaluating on paths beginning with a. The
linear-independence lift theorem explicitly assumes independence of each
shorter family and proves independence of their disjoint-support lifts.
This premise is appropriate and is not hidden inside a general
source-family independence claim.

## Axiom evidence and limits

All 17 audited declarations in the supplied logs report only `propext`,
`Classical.choice`, and `Quot.sound`. No additional axiom appears in those
outputs.

These modules establish general permutation validity, validity of the
exact restricted canonical family, numerator compatibility, and abstract
first-state lift facts. They do not yet establish:

- the closed cardinality formula for `SourceIndex`;
- an index bijection identifying canonical indices containing zero with
  the shorter family's lifted indices;
- equality of those canonical moments with the abstract lifts;
- independence of the remaining source columns;
- the residue reduction or all-horizon determinant nonvanishing.

In particular, the introductory explanation in `MomentLifts.lean` describes
the intended source-family recursion; its proved results are presently
the abstract lift facts, not that canonical-index recursion theorem.

## Addendum: exact cardinality

Read-only statement review of `SourceCounting.lean`: **PASS**. Compilation
and axiom certification remain the executor's responsibility.

The results count the actual `SourceFamily.SourceIndex`, retaining all
footnote-8 constraints. The proof classifies every nonempty admissible shared
set as its forced initial segment plus exactly one additional slot, counts
the complementary second divergent slots, and includes all three-valued
outcome assignments.

For N>=2, where the observation horizon is T=N+1, the subtraction-free
theorem states

\[
\#\mathrm{SourceIndex}(N)+\binom{3(N+1)}2=3^{N+1}+6N.
\]

The subtraction version correctly groups the positive terms before
natural-number subtraction. The recurrence

\[
\#\mathrm{SourceIndex}(N+1)
=3\,\#\mathrm{SourceIndex}(N)+3N(3N-2)
\]

has the correct horizon shift and agrees with the proposed lifted/new-index
counts. The specializations correctly give 162 at T5 and 606 at T6.

These results establish index cardinalities and their numerical recurrence.
They do not establish distinctness or independence of moment vectors, an
explicit recursive index bijection, or equality with first-state lifts.

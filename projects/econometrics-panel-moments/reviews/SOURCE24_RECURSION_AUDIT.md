# Independent statement audit: source recursion and conditional induction

15 October 2026. Read-only review by a separate Astra medium explorer agent;
no compilation or file changes were performed by the reviewer. This is an
internal statement audit, not external peer review.

**Result:** No semantic defect found in `PermutationLifts`, `SourceRecursion`,
`SourceLifts`, `SourceNewIndices`, or `SourceConditional`. The modules prove
exact source-index and moment-function recursion and a valid conditional
independence criterion. They do not establish independence of the new images
or generic source independence for arbitrary panel length.

## Findings

- `liftIndexEquiv` identifies a shorter canonical index plus a state with
  exactly the longer indices whose shared set contains zero. It shifts all
  old nonfinal slots, preserves the divergent label, and prepends the state
  to the ordered shared labels. Its inverse removes that shared initial slot;
  both directions preserve the actual admissibility restriction.
- `firstOrder_lift` and `secondOrder_lift` preserve the ascending remainder
  and fixed final slot. `sourceMoment_liftIndex` proves equality of real
  functions with the shorter first-state indicator lift. The inserted outcome
  is the shorter initial state, the table is `shift A`, and positivity
  justifies cancellation of the common first-transition scale.
- For `N >= 2`, `parameterEquiv` covers precisely the complementary indices
  at horizon `N + 2`. Their shared sets are empty or singleton, and their
  first divergent slot is zero. Singleton parameters put the divergent label
  `q₀` before the shared label `q₁`. Therefore the research-note notation
  `F_{t,s,a,b}` uses `a = q₁` and `b = q₀`.
- `conditionalTail` uses the actual shifted likelihood and every positive
  fixed-effect vector. Its kernel is exactly the functions whose first-state
  slices are shorter moments. No completeness or rank premise is needed.
- `linearIndependent_source_of_conditional` applies this map to a relation,
  removes inherited terms, uses the explicit new-image independence
  hypothesis to remove new coefficients, and then uses inherited independence.
  The `newParameters` version only reindexes that hypothesis. No independence
  assumption is concealed in a definition.

## Remaining bridges at the time of this review

The following paragraphs record the scope of the original review. The joint
map, actual normalization, ordered matrix products and reversible reduction
have since been proved in the continuation modules listed in STATUS.md.
The original review is not a retroactive audit of those later modules.

For fixed initial state `r`, the joint first-state image is coordinatewise
`transition A η 0 r a` times `conditionalTail A m a η`. This multiplier is
strictly positive on positive tables and effects, so it preserves kernels
and real linear relations. The reviewed modules do not formalize this
transport. In particular, the tail map is not literally the normalized
rational `F`-image in the research note.

The joint-map factorization, normalization, explicit `F` formulas, and
constant column operations still need formal proofs. Independence of those
new images remains open. These modules give pointwise statements for
positive tables; the nonvanishing economic witness and nonempty open dense
scalar-covariate conclusion remain separate obligations.

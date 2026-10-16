# Research roundup — 16 October 2026

This is the concise handoff for the equation-(24) continuation.
Research is still active until the user-set cutoff at 15:10
Europe/Amsterdam (13:10 UTC). The final stopping status will be
recorded here after the active responses and formal checks finish.

## Established results and their verification level

| Result | Status | Evidence |
|---|---|---|
| The 33 four-period source moments form a basis, for every initial outcome, on an explicit nonempty open dense joint economic parameter region | End-to-end Lean theorem; clean source rebuild and independent statement audit passed | [Precise theorem](THEOREM.md), [verification](VERIFICATION.md) |
| For every \(T\ge1\), the complete three-choice moment-space dimension is \(3^T-\binom{3T}{2}+6(T-1)\), on the stated joint economic generic region | End-to-end Lean theorem; clean source rebuild and independent statement audit passed | [Manuscript](MANUSCRIPT.md), [structural audit](reviews/STRUCTURAL_STATEMENT_AUDIT.md) |
| General source validity, exact index counts, actual recursive lifts and ordered matrix-product representations | Lean checked; these include conditional criteria, not the unresolved rank hypothesis | [Formal dependency map](DEPENDENCIES.md), [formal sources](formal/README.md) |
| Generic paired boundary independence, rank \(6m\) per state sector for every fixed \(m\ge2\) | Independently audited paper proof with an independently reconstructed exact finite initialization; substantial supporting Lean lemmas, with source bridges still open | [Invariant-tail proof](research/SOURCE24_INVARIANT_TAIL.md), [exact certificate](certificates/source24_invariant_tail_base.json) |
| Independence of the full particular equation-(24) family for every \(T\ge5\) | **Open** | Retained-old determinant (LC113)/(IT17), below |

The dimension theorem describes the entire moment space. It does not
by itself identify the paper's proposed list as a basis. The new paired
theorem settles the incoming boundary block in the current induction,
but leaves a different block of the full source determinant.

## What changed in this continuation

The successful specialization is
\[
 b_t=\frac{\tau a_t}{1+za_t}.
\]
After three explicit initialization steps, the accumulated weak image
is exactly the space of bounded rational functions vanishing at
\(0,\infty,z\). The actual forward transfer preserves that description
and adds three independent directions. The reset gauges are separated
by an explicit nonzero three-evaluation determinant.

The initialization uses actual two-block source coefficient vectors,
including their polynomial heads. A separate standard-library program
reconstructed 252 rational identities and the three coefficient matrices.
Their determinants reduce to \(162385,696500,789105\) modulo \(1000003\);
all required denominators are units. This finite calculation initializes
a uniform induction. Larger lengths are proved by the induction, not
inferred from numerical rank samples.

Lean has also checked nonsingularity of the exact displayed rational
matrices by integer column scaling and kernel-checked modular inverses.
The explicit two-block binary annihilation, retained heads, and weak
functions have also been derived in Lean from their displayed rational
H/J formulas. The concrete normalized tail extension has a Lean linear
equivalence and unique-decomposition theorem, with every factor condition
proved from explicit parameter intervals. The current aggregate passes
798 axiom checks in a 60-module closure.

The original source/time-derivative identification, the later finite
initialization, and the generic specialization are still separate formal
obligations. These results are not an end-to-end Lean paired theorem.

## The remaining mathematical problem

After eliminating the new boundary columns, the full source determinant
still contains
\[
 H_q=D_q+Z_T-Z_BC_B^{-1}C_T.
\]
Here \(D_q\) is the old source residue matrix. The new paired theorem
proves that \(C_B\) is generically invertible. The two \(Z\) terms and
\(C_T\) retain the insertion and polynomial-head corrections of the
actual source columns. Proving \(\det H_q\ne0\) uniformly is unfinished.

Several tempting shortcuts are invalid: paired rank and old rank alone
do not establish the joint rank; annihilating new poles does not erase
old double residues; and transporting a completed row does not transport
its polynomial head correctly without the stated correction.

## Approaches already explored

| Route | Established outcome | Remaining limitation |
|---|---|---|
| Direct finite source and residue certificates | Exact finite witnesses, including full source checks at \(T=5,6\) and residue checks through \(T=8\) | Finite evidence does not prove the all-\(T\) assertion |
| Near-diagonal common \(G\) | The natural leading diagonal and off-diagonal blocks have proved rank defects | Higher orders and their coupling remain possible |
| Rank-one common \(G\) | Local nine-column independence, followed by an explicit cross-time leading-rank obstruction | Local blocks cannot simply be assembled into the full determinant |
| Rank-one new earliest time, with old blocks fixed | Audited full-source regular-limit nullity at least \(3q(q-13)/2\); stronger \(3q(q-9)/2\) with regular correction coefficients | The regular zeroth-order limit is singular for large \(q\); actual higher jets remain open |
| Vandermonde common conic | Exact three-block residue rank \(51/54\), rational-row rank \(52\); later exact witnesses | The singular three-block base prevents an inverse-based induction starting there |
| Conic outgoing block and parity correction | Audited all-length outgoing nonvanishing, using the Lean binary parity theorem and a paper even-length correction | The regular/longitudinal source block remains |
| Conic regular leading operator | Exact corrected leading formula and a finite five-to-six-block witness | Uniform nonvanishing of the corrected operator is open |
| Directed elimination and source compression | Exact smaller inverse and kernel formulations using actual source coordinates | Compression preserves the unresolved transversality condition |
| Raw append, matching, axis and normal restrictions | Explicit ambient quotients, uniform partial pivots and smaller determinant targets | Coupled old-source corrections remain |
| Scalar prepend and deletion words | Uniform scalar spanning, actual lifts, odd incoming-rank theorem and further partial bounds | These auxiliary ranks do not prove the full source graph is transverse |
| Zero-prefix and prefix-graph recovery | Exact actual graph maps, including a five-monomial pencil in the new time parameters | Applying the map to corrected new columns still leaves a source-specific determinant |
| Simultaneous small-time and \(h=0\) limits | Proved saturation and valuation lower bounds; exact leading coefficients at prescribed finite lengths | The boundary loses directions and does not furnish a uniform nonzero coefficient |
| Generic nonzero-\(h\) transfer and Hermite quotient | Exact transfer, endpoint corrections, three-dimensional quotient and explicit cubic relation | Quotient multiplication is not valid; discarded actual relations matter |
| Invariant tail with nonzero \(z\) | **Closes generic paired independence for every length** | Source-to-formal-model bridges and the retained-old determinant remain |
| Full-source conic graph pencil | Exact cubic restriction with an affine transverse deformation | A nonzero generic pencil can vanish on the conic; corrected determinant nonvanishing is still required |

The Vandermonde common conic and the successful invariant tail are
different specializations. The former puts all state/time lines on one
dual conic; the latter generally has a different quadratic family for
each state. An obstruction for one cannot automatically be assigned to
the other.

Detailed derivations and finite certificates are retained in
[STATUS.md](STATUS.md) and the [research notes](research/).
Additional Pro responses on highest jets, old-weight limits, quotient
selectors and multiplication defects were consulted as exploratory
material. Their unintegrated claims are not part of the proved results.

## Future research, in priority order

1. Finish the actual-source bridges for the invariant-tail Lean proof:
   the source/time-derivative identification, forward promotion, later
   finite initialization, and generic specialization. The displayed
   two-block kernel and heads and the concrete bounded polynomial
   equivalence are now checked. Do not replace missing source bridges
   with an assumed rank statement.
2. Prove nonvanishing of \(H_q\), or an equivalent actual-source graph
   determinant, retaining all insertion and head terms. The paired
   theorem is now an available input to that problem.
3. Combine that result with the existing formal source recursion and
   polynomial criterion to obtain the full equation-(24) basis theorem,
   then verify its precise economic genericity statement.
4. Run the combined clean reproduction command in a fresh environment,
   refresh the bounded novelty search, and seek independent mathematical
   review before any publication claim.

The earlier component clean builds and statement audits remain valid.
A fresh-machine dependency download and a single combined clean run
have not yet been performed. Novelty and priority remain provisional;
no journal submission or author contact has been made.

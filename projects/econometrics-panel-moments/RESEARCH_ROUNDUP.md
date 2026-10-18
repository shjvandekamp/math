# Research roundup — 16 October 2026

Research stopped at the user-set cutoff, 15:10 Europe/Amsterdam
(13:10 UTC) on 16 October 2026. All accepted Pro runs had finished.
No optional research extension was used: no checked result brought the
remaining full-source determinant close enough to a proof. Only the
final verification and GitHub handoff continued after the cutoff.
The cutoff automation was paused; this snapshot is the stopping handoff.

## Established results and their verification level

| Result | Status | Evidence |
|---|---|---|
| The 33 four-period source moments form a basis, for every initial outcome, on an explicit nonempty open dense joint economic parameter region | End-to-end Lean theorem; clean source rebuild and independent statement audit passed | [Precise theorem](THEOREM.md), [verification](VERIFICATION.md) |
| For every \(T\ge1\), the complete three-choice moment-space dimension is \(3^T-\binom{3T}{2}+6(T-1)\), on the stated joint economic generic region | End-to-end Lean theorem; clean source rebuild and independent statement audit passed | [Manuscript](MANUSCRIPT.md), [structural audit](reviews/STRUCTURAL_STATEMENT_AUDIT.md) |
| General source validity, exact index counts, actual recursive lifts and ordered matrix-product representations | Lean checked; these include conditional criteria, not the unresolved rank hypothesis | [Formal dependency map](DEPENDENCIES.md), [formal sources](formal/README.md) |
| Generic paired boundary independence, rank \(6m\) per state sector for every fixed \(m\ge2\) | Independently audited paper proof with an independently reconstructed exact finite initialization; substantial supporting Lean lemmas, with source bridges still open | [Invariant-tail proof](research/SOURCE24_INVARIANT_TAIL.md), [exact certificate](certificates/source24_invariant_tail_base.json) |
| Generic nonvanishing of the actual three-class coefficient \(\mathfrak J_m\), for every fixed \(m\ge2\) | Second audited paper route to paired independence; 73 exact base checks and Lean determinant algebra | [Ordered-confluence proof](research/SOURCE24_CONFLUENT_QUOTIENT.md), [base certificate](certificates/source24_confluent_quotient_base.json) |
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

An independent ordered-confluence argument also closes the earlier
three-class coefficient route. It retains the actual zero-endpoint
space and endpoint sections, computes a nonzero even-length determinant,
and a nonzero first coefficient at odd lengths. A printed exploratory
matrix entry was corrected before acceptance. The exact two-block base
passed 73 identities; its endpoint adjuster also supplies the length-three
step. The confluence is a limit of actual spaces, not an assertion that
the literally coincident source matrix has full rank.

Lean has also checked nonsingularity of the exact displayed rational
matrices by integer column scaling and kernel-checked modular inverses.
The explicit two-block binary annihilation, retained heads, and weak
functions have also been derived in Lean from their displayed H/J
formulas over the reals, with exact rational constants. The actual
homogeneous-kernel derivative and constant source combination now give
the signed missing-output derivative, minus (r-z) times those weak
functions. The concrete normalized tail extension has a Lean linear
equivalence and unique-decomposition theorem, with every factor condition
proved from explicit parameter intervals. The literal rational transfer
and its new generators are now connected to those polynomial formulas.
The final verifier passed a clean rebuild of all 66 source-family modules
and all 1,013 declaration audits, using only standard foundational axioms.
The actual cubic matrix derivatives and the ordinary observation
determinants 397/2^37 and 3/256 are also now Lean checked.

The full source-family indexing, forward promotion, later finite
initialization, and generic specialization are still separate formal
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
| Ordinary update relative to the fixed old source matrix | Conditional on old invertibility, the update rank is at least \(\max(0,3q(q-13)/2)\) | A uniformly bounded ordinary-rank update cannot provide the proposed shortcut; displacement rank and a transported baseline are not excluded |
| Rank-two common-matrix degeneration | An audited cubic-order lower bound for the vanishing order of the actual raw residue determinant, positive from \(q=5\) | Nonvanishing of the first permitted coefficient remains open; singular row normalizations change the valuation |
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
| Ordered confluence of the actual three-class quotient | **Closes the alternative coefficient route at every length**, with separate even and odd coefficients | Full-source independence and formal confluence/source-space bridges remain |
| Full-source conic graph pencil | Exact cubic restriction with an affine transverse deformation | A nonzero generic pencil can vanish on the conic; corrected determinant nonvanishing is still required |
| Isolated triple collision and numerator jets | Audited Schur-preserving row change; 187 exact checks exhibit nonzero correction blocks in both old-pair directions | Simultaneous pair ordering cannot triangularize this fixture; the full transverse-jet correction remains |
| Marked conic limit of the actual source matrix | Audited regular marked extension, invertible residue/normal-jet conversion, and affine transfer retaining actual heads | Requires the corrected basis and incidence units; local pole factors do not settle the full Schur determinant |
| Full-source curved confluence | Actual integer column operations remove all first retained jets; for \(q\ge3\), at least \(3(q^2-5q+8)/2\) coefficient directions also vanish at second order | The intrinsic saturated-quotient valuation is not the raw residue determinant's valuation |
| Cubic circulation words | A nonzero ordinary three-column minor for every \(q\ge3\), supported by 54 exact checks and Lean base algebra | Its observations are already onto on new \(E_c\) columns, so the minor does not prove projected cubic independence |

The Vandermonde common conic and the successful invariant tail are
different specializations. The former puts all state/time lines on one
dual conic; the latter generally has a different quadratic family for
each state. An obstruction for one cannot automatically be assigned to
the other.

Detailed derivations and finite certificates are retained in
[STATUS.md](STATUS.md) and the [research notes](research/).
The latest full-source calculations are in
[collision jets](research/SOURCE24_COLLISION_JETS.md) and
[actual-source confluence](research/SOURCE24_SOURCE_CONFLUENCE.md).
The [marked conic limit](research/SOURCE24_CONIC_MARKED_LIMIT.md)
also records the corrected basis condition and an explicit three-block
exceptional incidence allowed by the originally stated positive bounds.
Additional Pro responses on highest jets, old-weight limits, quotient
selectors and multiplication defects were consulted as exploratory
material. Their unintegrated claims are not part of the proved results.

All accepted browser research runs finished before the cutoff. None
supplied a proof of full-source independence. Two proposed follow-ups,
on relative weak-time scales and a cyclic common matrix, were rejected
by the ChatGPT usage limit and were not carried out.

The following late responses are retained as leads for a future audit,
not as established results:

| Response | Reported direction | Audit status |
|---|---|---|
| [Pro55: multiscale return sector](https://chatgpt.com/c/6ad1ea9f-9608-83eb-a240-da5a6338c39b) | Higher-jet obstruction and an ordinary minor; the return-sector determinant remains open | New formulas not independently integrated |
| [Pro56: rank-two first coefficient](https://chatgpt.com/c/6ad1eae2-0ee4-83ed-a0fc-69180dc73555) | Further cancellation and a next kernel map | Latest follow-up not integrated into the audited valuation bound |
| [Pro58: chronological filtration](https://chatgpt.com/c/6ad1ee2e-f214-83eb-90ed-16a744b57f5b) | Finite nonnilpotence and polynomial-head feedback | Claimed finite checks not locally replayed |
| [Pro61: prefix-seed transport](https://chatgpt.com/c/6ad1f993-e268-83ed-af10-0177500354c5) | A completion-prefix discrepancy survives transport | Latest finite artifact not locally replayed |

These leads are distinct from the audited notes above. Cancellation on
a special path is not a counterexample to generic independence.

## Future research, in priority order

1. Finish the actual-source bridges for the invariant-tail Lean proof:
   full source-family indexing, forward promotion, later finite
   initialization, and generic specialization. The actual two-block
   kernel, heads, signed time derivative and concrete bounded polynomial
   equivalence are now checked. Do not replace missing source bridges
   with an assumed rank statement.
2. Prove nonvanishing of \(H_q\), or an equivalent actual-source graph
   determinant, retaining all insertion and head terms. The paired
   theorem is now an available input to that problem. One concrete
   confluence test at \(q=3\) is rank 51 of the second retained
   coefficient modulo the saturated actual new-source space, followed
   by a nonzero three-by-three projected cubic minor. Neither condition
   is proved. The existing ordinary cubic observations cannot serve
   as those quotient functionals.
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

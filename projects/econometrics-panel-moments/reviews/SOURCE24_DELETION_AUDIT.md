# Independent audit: deletion-word induction

**Result: PASS.** An independent Astra research reviewer checked equations
D1–D10 and the incoming-rank corollary in `research/SOURCE24_INDUCTION.md`.
The primary researcher also checked the argument before integration.

The paper argument establishes generic full column rank \(9k+3\) of the
scalar deletion-word double-residue matrix for every \(k\ge4\), using the
stated external exact base certificate.

## Base certificate

The saved \(k=4\) certificate uses
\[
G=\begin{pmatrix}1&1&1\\1&30&10\\1&3&2\end{pmatrix},
\qquad (u_t,v_t)=(8^t,8^{2t}),\quad t=1,\ldots,4.
\]
Its 39-by-39 minor is \(621903\) modulo \(1000003\), with the
residue-construction denominators nonzero modulo that prime. This establishes
a nonzero characteristic-zero rational minor. The certificate remains
external computation; the independent reviewer did not rerun it. The primary
researcher subsequently reproduced every saved deletion certificate exactly,
excluding runtime and resource metadata.

## Algebra and degeneration

- D2 is an exact parameter-dependent restriction after four generic finite-parameter boundary pivots. Those pivots need not remain nonzero at the degeneration limit.
- D3 is the exact reduced family. Its leading matrix is the smaller deletion family, with precisely five kernel coordinates when the induction hypothesis holds.
- D4 is the exact expression on that kernel.
- After canceling the first-block state-one and state-two denominators, the selected moving-line residues extend analytically. Their constant terms vanish on the entire reduced family. The explicit degeneration factor makes their first coefficients evaluations at the limiting axis; cross-point motion contributes only at higher order.
- All five rows in D5 annihilate the entire leading matrix. Consequently elimination of leading pivots cannot alter the stated first-order kernel map.
- D6 first detects the two coefficients of the binary form \(p\), then the two coefficients of \(s\), leaving exactly \(q_{10}=cX_0\).
- The fixed old-tail row in D8 detects that remaining coordinate. Thus the five kernel derivatives are independent and D9 gives a nonzero reduced minor.

## Common-transition parameter space

The nonvanishing arguments preserve a single common \(G\). Binary
propagation uses its nonzero binary minor and distinct restricted poles.
For D8, the final time parameters are independent of the selected cross-point;
distinct reciprocal denominators detect the surviving nonzero row. The
required nonzero polynomial conditions can be intersected on the same
irreducible parameter space and within the positive parameter orthant.

## Incoming-rank corollary and limits

H17 transfers full deletion rank to the remaining \(9m-6\) auxiliary
incoming columns. The previously audited six boundary pivots combine with
these through an exact block-triangular support pattern. Subject to the earlier
polar hypotheses identifying the auxiliary family with the actual operator,
this proves generic rank \(9m\) of \(Z_{-3}\) for odd \(m\ge5\).

This is an audited paper proof with an external computational base case, not
a Lean theorem. It does not establish injectivity of \(B_0O^{-1}\) on the
incoming image, nonvanishing of the full regular determinant, or independence
of the specified source family for every horizon.

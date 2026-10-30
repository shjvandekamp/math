# The append commutator on actual seed residues

**Status: independently audited paper calculation.** The results
below concern old pair data only. They neither prove an incoming quotient
rank nor bound the terminal boundary determinant. No computation or Lean
formalization is used here.

Use the marked completed seeds \(R_{tA}\) from C6 in
`SOURCE24_COMPLETION_QUOTIENT.md`, with \(q\ge2\) old blocks.
Their pair data equal those of the zero-sum rows \(U_{tA}\), because
\(R_{tA}=U_{tA}-V_{tA,0}\) and \(V\) has no pair residue.
Let \(S=\rho(R_{tA})=\rho(U_{tA})\), with \(3q\) columns.
Assume the generic old geometry and binary invertibility required by
these seeds: pair points have nonzero coordinates, the local two-vector
residue bases are independent, and all defining axis evaluations exist.

Write the positive, invertible common matrix as
\(G=(\mathbf1,\alpha,\beta)\), and put
\[
 w=e_2G^{-1},\qquad E=e_2^{\mathsf T}w.
\]
Thus \(w\mathbf1=0\), \(w\alpha=0\), \(w\beta=1\),
and \(rE=r_2w\). In particular all pair rows and \(w\) lie
in the two-dimensional zero-sum plane \(\mathsf H\).

## A common-G degeneration with an invertible first coefficient

Append a block with
\[
 A_{q+1}=G\operatorname{diag}(1,\eta u_*,\eta v_*),
 \qquad u_*,v_*>0.
 \tag{A1}
\]
At any fixed old pair point, \(X_0\ne0\), so its kernel is
analytic in \(\eta\). Its expansion is
\[
 K_{q+1}=\mathbf1e_0+\eta\left[
 u_*\frac{X_1}{X_0}\alpha(e_1-e_0)
 +v_*\frac{X_2}{X_0}\beta(e_2-e_0)\right]+O(\eta^2).
 \tag{A2}
\]
For \(r\in\mathsf H\), both products in the constant
commutator vanish. The first term involving \(\alpha\) also
vanishes in the commutator, since \((e_1-e_0)_2=0\) and
\(w\alpha=0\). Therefore
\[
 r[K_{q+1},E]
 =\eta v_*\frac{X_2}{X_0}\,\mathcal C(r)+O(\eta^2),
 \qquad
 \mathcal C(r)=(r\beta)w-r_2(e_2-e_0).
 \tag{A3}
\]

The coefficient \(\mathcal C\) is a fixed state operator, independent
of the old point and of \(u_*,v_*\). In the basis
\((e_0-e_1,e_2-e_0)\) of \(\mathsf H\),
\[
 \begin{split}
 \mathcal C(e_0-e_1)&=(\beta_0-\beta_1)w,\\
 \mathcal C(e_2-e_0)&=(\beta_2-\beta_0)w-(e_2-e_0).
 \end{split}
\]
Its determinant is
\[
 \det(\mathcal C|_{\mathsf H})=(\beta_0-\beta_1)w_1.
 \tag{A4}
\]
Here \(w_1\) means the component indexed by state one. Assume
\((\beta_0-\beta_1)w_1\ne0\), a nonempty generic condition
within positive invertible common matrices. For example,
\(w_1=(\alpha_0-\alpha_2)/\det G\).

Then \(\eta^{-1}[K_{q+1}(P),E]|_{\mathsf H}\) has an
invertible limit at every old pair point \(P\). Since there are
finitely many points, the blockwise operator on all old pair data is
invertible for generic sufficiently small nonzero \(\eta\).
The assertion uses actual positive \(\eta\), with generic full
line geometry restored away from its proper exceptional set. The
colliding configuration at \(\eta=0\) is only an expansion point,
not a claimed admissible instance.

## The actual seed matrix has rank \(3q\)

For \(q\ge3\), R10–R11 of
`SOURCE24_RESIDUE_DIFFERENCES.md` give
\(\mathcal DS=I-e\gamma^{\mathsf T}\), with an explicit
inverse. Hence \(S\) has rank \(3q\), without an old source
inverse.

The two-block case has a separate direct proof. Let \(r\ne t\)
be the other block. The pair data of
\[
 U_{tA}=F_{t,r,A,0}-c_{tA}F_{r,0}
\]
are supported on the star of pairs \((r,0),(t,a)\), and
\(c_{t0}=0\). The stars for \(t=1,2\) meet only at the
pair \((1,0),(2,0)\). In a relation among the six seeds, write
its coefficients as \(x_{tA}\) and
\(C_t=\sum_Ac_{tA}x_{tA}\). At a leaf with \(a=1,2\),
the residue is
\[
 X_aX_0\left[-x_{ta}v_{r0}
                    +C_tA_r(0,a)v_{ta}\right].
 \tag{A5}
\]
The two vectors are independent and the scalar factors are nonzero,
so all four leaf coefficients vanish. The remaining central residues
are \(-X_0^2v_{20}\) and \(-X_0^2v_{10}\), also independent.
Thus \(\operatorname{rank}S=6\) for \(q=2\). This argument
again needs no invertibility assertion about the full old source matrix.

## Rank of the old-node discrepancy

The append identity for the marked seeds has a correction with at most
one old pole. Consequently its old pair data are \(rK_{q+1}\).
The coordinate transfer \(\mathcal A_B\) acts at an old node by
\((P_B/P_2)rE\). Thus the old-node discrepancy between transfer
after append and append after transfer has columns
\[
 \Delta_{B,tA}(P)
  =\frac{P_B}{P_2}\,
          \rho_P(R_{tA})[K_{q+1}(P),E].
 \tag{A6}
\]
This recovers T12 of `SOURCE24_TERMINAL_PEELING.md`
directly on old nodes; it does not assume the rest of that conditional
recursive construction.

For each fixed \(B\), all factors \(P_B/P_2\) are nonzero.
The invertible blockwise operator (A3) therefore preserves the seed
rank. For every \(q\ge2\), the \(3q\) columns in that one
sector have generic rank
\[
 \operatorname{rank}\Delta_B=3q.
 \tag{A7}
\]
Equivalently, their first nonzero coefficient after division by
\(\eta\) already has rank \(3q\). The discrepancy is not a
fixed finite-rank correction independent of length.

There is a stronger combined statement at odd \(q\ge5\), using
the independently audited deletion/incoming theorem. That theorem says
the \(9q\) scalar-direction pair columns
\[
 A_t(A,B)\frac{P_B}{P_2}
              (\rho_P(R_{tA}))_2w
\]
are generically independent. Dropping the nonzero column factors and
undoing the component-two projection shows that the vector pair columns
\((P_B/P_2)\rho_P(R_{tA})\) are also independent. By (A3),
the leading combined discrepancy is an invertible blockwise operator
applied to that same vector family. Hence, on the intersection of the
stated nonempty generic parameter sets,
\[
 \operatorname{rank}[\Delta_0\mid\Delta_1\mid\Delta_2]=9q,
 \qquad q\ge5\text{ odd}.
 \tag{A8}
\]
This last conclusion is conditional on the audited scalar incoming
theorem; it is not a new proof of that theorem. No combined-rank
assertion is made here at other lengths.

## What this does and does not settle

The actual seed commutator has full column rank in each sector, and in
the combined family at the lengths covered by (A8). It therefore cannot
be discarded as a correction of constant rank, or moved exclusively to
new-node observations. Equations (A2)–(A3) give a concrete leading
transport law if a recursion keeps the full vector pair data.

These are ranks before quotienting by the actual completion span.
They neither imply nor contradict injectivity in that quotient, and do
not prove the determinant in T10 is nonzero. Control of that quotient
and its boundary coupling remains necessary.

An independent Astra reviewer checked the expansion, two-dimensional
determinant, separate two-block seed argument, generic-set intersection,
and both rank deductions. The primary researcher checked the state-operator
calculation and the distinction between pair-data rank and quotient rank.

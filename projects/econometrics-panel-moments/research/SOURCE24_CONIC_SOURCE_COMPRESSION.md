# Conic leading operator: one source seed and an explicit kernel

**Status: independently audited paper identities; not Lean formalized.**
These reductions were proposed in the
[Pro18 investigation](https://chatgpt.com/c/6ad1564a-523c-83eb-8250-6eed3cc18bc2)
and checked locally. They compress the old inverse in the
[regular leading operator](SOURCE24_CONIC_REGULAR_LEADING.md), preserve
the even first-jet correction, and identify a small image of the source
seed. They do not prove the remaining determinant nonzero.

Use that note's conic parameters, literal move-first words, and residue
conventions. Let n be the number of old blocks, d=9n(n−1), and
\(i=(t,A)\), \(r_i=\alpha_A b_t\), \(h_i=X_A/L_{tA}\).
The old coefficient space has standard vectors
\(e_{t,s,A,b}\). The matrix O records double residues of the actual
sources F; U records the divided simple residues of the positive raw
rows \(\widehat Q\). In particular these two maps have the sign
conventions of the preceding note, not a shared raw-row convention.
Every inverse of O below assumes it is invertible. No statement
inverts the singular conic O at n=3.

## One actual-source seed

Set \(r(t)=\min\{s:s\ne t\}\) and define coefficient matrices
with 3n columns by

\[
 \mathsf E_i=e_{t,r(t),A,0},\qquad
 \mathsf V_{s,j}=\sum_{b=0}^2e_{s,r(s),j,b}.
 \tag{SC1}
\]

The actual words give

\[
 \begin{split}
 \widehat Q(\mathsf E_i)&=X_0h_i e_0P^{\widehat t},&
 F(\mathsf E_i)&=X_0h_i e_0(I-P^{\widehat t}),\\
 \widehat Q(\mathsf V_{s,j})&=X_je_jP_s,&
 F(\mathsf V_{s,j})&=X_je_j(K_s-P_s).
 \end{split} \tag{SC2}
\]

After removing the incoming factor \(r_i^c\), the transverse
elimination for new state c depends on c only through
\(x_c=\alpha_c\epsilon\). Its analytic constant is therefore a
single matrix \(\lambda\), with rows \((s,j)\) and columns i.
Writing \(\mathsf R=\operatorname{diag}(r_i)\), the sector constants
are \(\Lambda_0^{(c)}=\lambda\mathsf R^c\). Put

\[
 Y=\mathsf E-\mathsf V\lambda.
 \tag{SC3}
\]

At a cross-pair node \(P_{ik}=(r_ir_k,-r_i-r_k,1)\), let
\(\mathsf X_c\) multiply both retained residue components by its
coordinate \(X_c(P_{ik})\). Then

\[
 Z_0^{(c)}=\mathsf X_c\mathsf X_0^{-1}OY\mathsf R^c.
 \tag{SC4}
\]

Indeed, after extracting \(r_i^cX_c/X_0\), the limiting corrected
incoming row is
\(X_0h_i(e_c-e_0P^{\widehat t})-
\sum_{s,j}\lambda_{sj,i}X_je_j(I-P_s)\).
Subtracting F(Y_i) leaves

\[
 X_0h_i(e_c-e_0)-
 \sum_{s,j}\lambda_{sj,i}X_je_j(I-K_s).
 \tag{SC5}
\]

These terms have at most one old-line pole. Multiplication by
\(X_c/X_0\) creates none at the old cross-pair nodes, where X0 is
nonzero. Their double residues vanish, proving (SC4).

Let \(\mathscr E z=z_2\ell_2\), retaining components 0,1 and using
\(z_2=-z_0-z_1\), where \(\ell_2=e_2G_\alpha^{-1}\).
The preceding note's operator is \(D=\mathsf X_0\mathscr E\).
Thus the leading matrix, grouped by new state, is

\[
 \mathfrak H=UO^{-1}DZ_0
  =[UO^{-1}\mathsf X_0\mathscr E OY,\,
    UO^{-1}\mathsf X_1\mathscr E OY\mathsf R,\,
    UO^{-1}\mathscr E OY\mathsf R^2].
 \tag{SC6}
\]

Removing the invertible right scalings defines \(\widetilde{\mathfrak H}\)
and gives
\(\det\mathfrak H=(\det\mathsf R)^3
\det\widetilde{\mathfrak H}\), where
\((\det\mathsf R)^3=(\alpha_0\alpha_1\alpha_2)^{3n}
\prod_t b_t^9\). In particular all three sectors come from the
same actual-source matrix Y.

There is also a scalar-node description. Let \(\pi_2\) extract
component 2 at each node, let \(\jmath_\ell\) insert a scalar times
\(\ell_2\), and put \(T=\pi_2OY\),
\(\mathcal L=UO^{-1}\jmath_\ell\). Then

\[
 \widetilde{\mathfrak H}=
 \mathcal L[\operatorname{diag}(r_ir_k)T,
             -\operatorname{diag}(r_i+r_k)T,T].
 \tag{SC7}
\]

## An explicit kernel and exact compression

For n at least 3, let
\(\mathscr C_0=\operatorname{span}\{e_{t,s,A,b}: A=0\text{ or }b=0\}\),
of dimension \(5n(n-1)\). Let \(\Pi_0\) select U's 3n rows
with old state zero, and let \(\Pi_{\rm bin}\) select its other 6n rows.
Then, generically in the conic parameters,

\[
 U(\mathscr C_0)=\text{the entire state-zero observation space}.
 \tag{SC8}
\]

Here is a direct proof, including the normalized residues at X0=0.
Set \(J_t=\operatorname{diag}(X)K_t\operatorname{diag}(X)^{-1}
=\operatorname{diag}(h_{ta})A_t\). The scalarized raw row is

\[
 \widehat Q_{t,s,A,b}\operatorname{diag}(X)^{-1}
 =h_{tA}r_{tA}^{\,b}e_bJ_s\prod_{u\ne t,s}^{\uparrow}J_u.
 \tag{SC9}
\]

At X0=0 each J has zero first row. Cancel the old pole and divide
by its arrival coordinate before evaluating, as required by U.
If A=0 and b>0, only the rows on line (t,0) can survive. If A>0 and
b=0, only the rows on the first tail line (s,0) can survive. If A=b=0,
every row vanishes: a single divided residue cannot cancel both input
factors X0. This proves containment in (SC8).

For a fixed t, use the sources with A=0, b=1,2, and s equal to the
largest or second-largest block other than t. Their only observations
are in the t block. The active binary factors are invertible at
\(Q_{t0}=(0,-r_{t0},1)\). Consequently the two starting rows for a
fixed s span the plane of active rows of its literal terminal block.
The two choices of s give terminal blocks k and l in the opposite
order. The three rows \(A_k(1,:),A_k(2,:),A_l(1,:)\) are independent
by the Vandermonde determinant at
\(\alpha_1b_k,\alpha_2b_k,\alpha_1b_l\). This proves surjectivity.

Choose a nonzero 3-column minor separately for each t to construct a
parameter-only right inverse R0 into \(\mathscr C_0\), with
\(UR_0=\iota_0\), the state-zero coordinate inclusion. Therefore

\[
 \mathscr K_0=(I-R_0\Pi_0U)\mathscr C_0
   =\mathscr C_0\cap\ker U,\qquad
 \dim\mathscr K_0=n(5n-8).
 \tag{SC10}
\]

Let \(Y_{\rm ker}\) be a basis of this kernel and let Ebin embed
the standard source coordinates A,b in {1,2}. Define

\[
 \mathcal C=[R_0,\ E_{\rm bin}-R_0\Pi_0UE_{\rm bin}],
 \qquad p=n(4n-1).
 \tag{SC11}
\]

The matrix \([Y_{\rm ker},\mathcal C]\) is a basis of the full
d-dimensional coefficient space, and
\(U\mathcal C=\operatorname{diag}(I_{3n},U_{\rm bin})\), where
\(U_{\rm bin}=\Pi_{\rm bin}UE_{\rm bin}\). No full-rank claim for
Ubin is needed here.

Assume O invertible. Choose a quotient map Xi of rank p with kernel
\(O\mathscr K_0\), and put \(\widehat O=\Xi O\mathcal C\).
It is invertible, and decomposition in the displayed coefficient basis
gives the exact identity

\[
 UO^{-1}=U\mathcal C\widehat O^{-1}\Xi.
 \tag{SC12}
\]

This replaces an inverse of order \(9n(n-1)\) by one of order
\(n(4n-1)\). Xi can be constructed from the residue matrix of the
explicit kernel; it does not require O inverse. Substitution into
(SC6) gives

\[
 \widetilde{\mathfrak H}
 =U\mathcal C\widehat O^{-1}\Xi
   [\mathsf X_0\mathscr E OY,\mathsf X_1\mathscr E OY,
    \mathscr E OY].
 \tag{SC13}
\]

## The sparse seed's terminal defect

Put \(p_t=\alpha_1b_t\), \(\gamma_t=\alpha_2b_t\), and

\[
 d_t(y)=\frac{y(p_t-\gamma_t)}{(p_t-y)(\gamma_t-y)},\qquad
 \tau_t(y)=\frac{p_t+\gamma_t-y}{p_t\gamma_t}.
 \tag{SC14}
\]

Define \(\chi_i=(h_i/d_t)(0,-r_{r(t),0},1)\) and
\(\lambda^{\rm sp}_{(s,j),i}
=\mathbf1_{s=r(t)}\mathbf1_{j=0}\chi_i\), with
\(Y^{\rm sp}=\mathsf E-\mathsf V\lambda^{\rm sp}\).
The established odd-parity formula says Y equals this sparse seed for
odd n. Its following property holds for either parity:

\[
 UY^{\rm sp}=u_*\eta,
 \tag{SC15}
\]

where u* is the coordinate ((1,0),output 0) and eta is supported only
on columns (n,1),(n,2). With \(y_*=r_{10}\), its entries are

\[
 \eta_{(n,A)}=h_{nA}(0,-y_*,1)\,y_*
   \prod_{j=2}^{n-1}d_j(y_*)
   [\tau_{n-1}(y_*)-\tau_n(y_*)],
 \qquad A=1,2.
 \tag{SC16}
\]

To check all factors and the sign, the raw seed is exactly
\(X_0[h_i e_0P^{\widehat t}-\chi_i e_0P_{r(t)}]\).
Its only possible divided residue is on the first remaining state-zero
line (r(t),0). The binary zero-sum row propagates by the product of the
binary determinants. The full word has one extra factor dt, so the
choice chi cancels outputs 1,2. A scalarized row w ending in block k
and with zero-sum binary part has \(w_2=yw_1\) and
\(w_0=\tau_k(y)w_1\), as follows from the plane spanned by
\(A_k(1,:),A_k(2,:)\). Both words end in n unless t=n. In that
exception the deletion word ends in n−1 and its divided residue has
\(w_1=y_*\prod_{j=2}^{n-1}d_j(y_*)\), proving (SC16).

The seed itself has rank 3n: its positive-initial-state coordinates
give 2n distinct unit pivots and its A=0 columns are distinct unit
sources (chi is zero there). Eta is generically nonzero, with the
additional open condition \(\tau_{n-1}(y_*)\ne\tau_n(y_*)\).
That inequality is not asserted at every distinct-node fixture.
Thus UYsp generically has rank one. Since Ysp lies in C0, (SC10)
also gives \(\operatorname{rank}(\Xi OY^{\rm sp})=1\).
This is not a rank obstruction to (SC13): its three coordinate
operators act before Xi and need not preserve the kernel.

## Keeping the even correction

In the even first-jet notation, write K and L for right and left
kernel bases of the binary leading matrix and
\(J=L\Sigma'(0)K\). Assume its required generic inverse exists.
The state-zero incoming equation gives
\((D^{-1}q_{1,0},0)^\mathsf T=\lambda^{\rm sp}\) in either
parity, by the same first-pole determinant ratio used above. Set

\[
 V_* =\begin{pmatrix}-D^{-1}A'(0)K\\K\end{pmatrix},\qquad
 G_*=L(q_{1,b}-BD^{-1}q_{1,0}),\qquad C_*=\mathsf V V_*.
 \tag{SC17}
\]

Here D,A,B are the transverse block matrices, not the node operator D
used before (SC6). The established even formula becomes
\(Y=Y^{\rm sp}-C_*J^{-1}G_*\). Its additional coefficient-space
image has dimension at most two, so \(\operatorname{rank}(UY)\le3\).

Let \(\mathcal T_c=O^{-1}\mathsf X_c\mathscr E O\), set
\(H^{\rm sp}=[U\mathcal T_0Y^{\rm sp},
U\mathcal T_1Y^{\rm sp},U\mathcal T_2Y^{\rm sp}]\), and put
\(A_*=[U\mathcal T_0C_*,U\mathcal T_1C_*,U\mathcal T_2C_*]\),
\(B_*=\operatorname{diag}(G_*,G_*,G_*)\),
\(J_*=\operatorname{diag}(J,J,J)\). Then

\[
 \widetilde{\mathfrak H}=H^{\rm sp}-A_*J_*^{-1}B_*,\qquad
 (\det J)^3\det\widetilde{\mathfrak H}
 =\det\begin{pmatrix}H^{\rm sp}&A_*\\B_*&J_*\end{pmatrix}.
 \tag{SC18}
\]

The six-column border does not assume Hsp invertible. The state-zero
Schur contribution is present in V*. What remains is to control the
three transformed copies of the seed in (SC13), including this border
in even parity. Neither the kernel dimension nor the small untransformed
seed image proves that mixed-coordinate matrix invertible.

## A single-pole correction for the transformed lift

There is an explicit rational lift of the transformed node data. For
an old coefficient vector v, write R=F(v), h=R2/X2, and put
\(B_c=X_ch\ell_2\). This is a homogeneous, degree-one, zero-sum
row with only old-line poles. At the chosen pair representatives X2=1,
so its double residues are exactly
\(\mathsf X_c\mathscr E Ov\). If O is invertible, let
\(R_c=F(O^{-1}\mathsf X_c\mathscr E Ov)\). Their difference has
no double residues, including same-block pairs. It consequently has
the form

\[
 R_c-B_c=L(X)+\sum_i\frac{Q_i(X)}{L_i(X)},
 \tag{SC19}
\]

where L is a linear zero-sum row and each Qi is a quadratic zero-sum
row, taken modulo Li. To prove this, restrict each simple-pole residue
to its projective line. The vanishing double residues remove all its
remaining poles, leaving a quadratic section. Subtract polynomial
lifts of these sections; the remaining row is a linear polynomial.
This repair space has dimension at most \(6+6(3n)=18n+6\).

The explicit lift Bc generally fails componentwise coordinate
divisibility. Repairing ambient membership does not select the actual
source lift uniquely: the zero-pair part of the old zero-sum ambient
space still has 3n dimensions. Moreover, U acts on the positive raw
row, so its prefix must also remain:
\(\widehat Q(O^{-1}\mathsf X_c\mathscr E Ov)
=I(O^{-1}\mathsf X_c\mathscr E Ov)-B_c-(R_c-B_c)\).
Divided matching residues must be evaluated only after these terms
are combined and their coordinate factors canceled. Thus (SC19)
localizes the unknown correction to simple poles; it does not prove
kernel invariance or remove the actual-source condition.

## Exact finite reconstruction

The local verifier
[source24_conic_source_compression.py](../exploration/source24_conic_source_compression.py)
and its [saved results](../exploration/source24-conic-source-compression-results.json)
use the earlier n=5 fixture: alpha=(1,2,3), old times
(1,5,25,125,625), and prime 1,000,003. It constructs E, V and Y
from the actual source coefficients and checks (SC2) and every sector
of (SC4). The divided U map is separately checked using actual kernel
products with coordinate factors canceled before evaluation.

The image of C0 has rank 15. The explicit kernel has 85 basis
columns, and its complement has 95. The quotient matrix has
determinant 670647. The verifier checks
\(U\mathcal C(\Xi O\mathcal C)^{-1}\Xi O=U\)
on all 180 source columns, without computing O inverse. The seed has
rank 15, and UY and Xi OY both have rank one, with exactly the
terminal defect (SC16). The two nonzero eta entries are 686958 and
869797 modulo the prime; their rational signs are respectively
positive and negative.

After restoring the sector scalings and recorded column permutation,
the compressed leading matrix equals the earlier 45-square matrix
entrywise, with determinant 214966. The unscaled grouped determinant
is 785694, and the grouping permutation has sign −1. These are
finite normalization checks, not an all-length determinant proof.
The guarded run exited zero in 1.663260458 seconds using 26,640,384
bytes maximum RSS, with no resource cutoff. It does not implement
the even-parity correction.

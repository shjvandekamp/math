# Transverse pivots for a conic append

**Status: independently audited paper derivation; not Lean formalized.**
The user-authorized [GPT-6 Pro investigation](https://chatgpt.com/c/6ad13838-08fc-83ed-aa54-8025b249a045)
supplied the uniform 9n−6 block below. The primary researcher checked its
normalizations, endpoint support and retained Schur corrections. No
all-length source nonvanishing is asserted.

Assume n>=1, distinct positive alpha values, and distinct positive old
nodes q_ta=alpha_a b_t. Use nonzero append parameters outside all collision
loci. Invertibility of O_n is an additional hypothesis only for CT8.

Use n old conic blocks and append block m=n+1 with b_m=epsilon.
At its state-c line put x=alpha_c epsilon, and parametrize that line by
X(x,y)=(xy,−x−y,1). Let

\[
 v_x=(xy,-x(x+y),x^2),\qquad h_x=(x,0,-y)^T,
 \quad \tau(z)=\frac{zh_x}{(y-x)X_c},\quad \eta(z)=z_2/x^2. \tag{CT1}
\]

At each new/old node y=q_ta these are invertible coordinates on the
zero-sum residue plane: tau(v_x)=0 and eta(v_x)=1. Every interior
completed word ends in K_m, so its new-line residue is proportional to
v_x. Thus tau annihilates all old source columns exactly. The longitudinal
old-column entry is
−[(L_ud Qhat_i^(n))_c](P_(x,q_ud)); it is generally nonzero.

Let P_s use all old blocks, move-s-first, and let P^t use the increasing
old word with t omitted. Ordinary one-variable residues at y=q_ua give
the exact transverse entries of the two new source types:

\[
 \tau\rho F_{m,s,c,b}
   =\operatorname{Res}_{y=q_{ua}}[v_{x,b}e_bP_sh_x],\qquad
 \tau\rho F_{t,m,A,c}
   =\operatorname{Res}_{y=q_{ua}}
     \left[\frac{X_Aq_{tA}^c}{(q_{tA}-x)(q_{tA}-y)}v_xP^th_x\right].
 \tag{CT2}
\]

The signs follow from L(q)(X(x,y))=(q−x)(q−y) and the minus completed
term in F. Each new column has support in just its state-c sector.

## A uniform controlled outgoing block

Normalize outgoing columns as C_s0=F_msc0/x, C_s1=F_msc1/x,
C_s2=F_msc2/x². Their transverse entries extend analytically to x=0.
Write r_t=q_t0, beta_t=q_t1, gamma_t=q_t2. At x=0 the binary kernels are

\[
 B_t(y)=\begin{pmatrix}-y/(\beta_t-y)&\beta_t/(\beta_t-y)\\
                         -y/(\gamma_t-y)&\gamma_t/(\gamma_t-y)\end{pmatrix},
 \quad d_t(y)=\frac{(\beta_t-\gamma_t)y}{(\beta_t-y)(\gamma_t-y)}.
\]

Let f_s be the output-two entry from state one of the actual move-first
binary product and D=prod d_t. The limiting scalar residue functions of
the normalized columns are respectively

\[
 -y^2(P_s(0,y))_{02},\qquad y^2f_s,\qquad -y(f_s+D). \tag{CT3}
\]

At a state-zero node r_t, only C_t0 has a pole. Its pivot is
delta_t=r_t³ prod_(j!=t) d_j(r_t), nonzero under the conic geometry.
This supplies n pivots per sector.

Set Q(y)=prod_t(y−beta_t)(y−gamma_t) and
T_s=Q(f_s−f_1), for s=2,...,n. These polynomials have support

\[
 T_s=\ell_s y^{n-s+1}+\cdots+h_s y^{n+s-1},\quad
 \ell_s=Q(0)(\gamma_{s-1}^{-1}-\gamma_s^{-1})
          \prod_{j>s}\frac{\beta_j-\gamma_j}{\beta_j\gamma_j},\quad
 h_s=(\beta_s-\beta_{s-1})\prod_{j>s}(\beta_j-\gamma_j). \tag{CT4}
\]

To prove the endpoints, the move-s-first and move-one-first words share
the suffix B_(s+1)...B_n. Their prefix difference is zero-sum and is
multiplied by the scalar product of the suffix determinants. For a prefix
of length at least two, the first-order expansion at zero depends only on
its last block, as 1+y/gamma_last+O(y²). At infinity it is
−beta_last/y+O(y^−2). The two last blocks are s−1 and s, yielding CT4.
Every endpoint is nonzero for distinct positive old nodes.

Use outgoing differences A_s=C_s2−C_12 and B_s=C_s1−C_11.
On binary-node transverse rows apply the invertible interpolation map

\[
 \mathcal I(r)(y)=\sum_{z\in\{\beta_t,\gamma_t\}}
                 \frac{r_z}{z^2}\frac{Q(y)}{y-z}. \tag{CT5}
\]

The limiting columns become −T_s/y and T_s. Select coefficient rows
n−s and n+s−1. Their diagonal two-by-two block is diag(−ell_s,h_s);
every earlier pair has support strictly inside these two exponents.
Together with the state-zero pivots this gives, per sector,

\[
 \Delta_n=(-1)^{n-1}\prod_t\delta_t\prod_{s=2}^n\ell_sh_s\ne0.
 \tag{CT6}
\]

For all three sectors the controlled matrix H has size 9n−6 and
det H(epsilon)=Delta_n³+O(epsilon). The remaining outgoing columns are
C_11,C_12 in each sector. Their interpolated limiting representatives are
N_1=Qf_1 and (Q−N_1−c_D y^n)/y, where c_D=prod(beta_t−gamma_t).
The second is polynomial because N_1(0)=Q(0). Eliminating the outer
CT4 coefficients leaves only degrees n−1 and n. This explicitly specifies
the two-dimensional outgoing remainder.

For the undifferenced state-two column, the divided-residue function
−(f_s+D)/y has the additional principal part −1/y at zero. Adding 1/y
removes that pole without changing any binary-node residue. The result
(1−f_s−D)/y is proper and regular at zero, so CT5 gives its product
with Q without a polynomial ambiguity. For the difference columns this
principal part cancels directly.

## Exact remaining Schur matrix

Order columns as old, controlled outgoing, and remaining new. Order rows
as old/old, controlled transverse, remaining transverse, longitudinal.
The transformed matrix is

\[
 \begin{pmatrix}
 A&B_p&B_r\\0&H&J\\0&H_0&J_0\\C&D_p&D_r
 \end{pmatrix}. \tag{CT7}
\]

At an old/old node the old-column residue is its former residue multiplied
by K_m. Thus A is invertible whenever O_n is, and
det A=det O_n times the product of det K_m over all old/old nodes.
The block C is the explicit longitudinal contribution described after CT1.
Eliminating A and H gives the square remaining matrix

\[
 \mathcal R_n=\begin{pmatrix}
 J_0-H_0H^{-1}J\\
 D_r-CA^{-1}B_r-(D_p-CA^{-1}B_p)H^{-1}J
 \end{pmatrix},\qquad \dim\mathcal R_n=9n+6. \tag{CT8}
\]

Its determinant, multiplied by det A det H, is the transformed full
determinant. Both old-node correction terms remain. Only H was evaluated
at epsilon=0; A^-1 may have poles there. Neither boundedness of A^-1 nor
nonvanishing of det R_n is assumed. This is a conditional induction
criterion, not its conclusion.
In particular O_3 is singular throughout the conic family, so CT8 does
not supply the conic three-to-four-block step.

## Connection to the existing binary parity theorem

The primary researcher observed a further identification, independently
checked by a second Astra researcher. Before taking differences, CT5 sends the binary
outgoing columns to Q f_s and Q r_s/y, where r_s is the opposite
off-diagonal entry of the binary product. Indeed
1−f_s−D=r_s. With w=−1/y the binary kernels are precisely the established
common-rho family, c_t=beta_t and rho=gamma_t/beta_t=alpha2/alpha1.
The two function lists become q(P_s) and −w r(P_s), up to the common
nonzero Q. Their residue representation is injective by the regular
interpolation argument. Hence the known rank theorem gives total
outgoing transverse rank 9n at the limit for odd n and 9n−6 for even n.
The subsequent [uniform even correction](SOURCE24_CONIC_EVEN_JET.md)
settles the six missing directions by a first-kernel derivative. Its
positive common-alpha witness proves generic outgoing transverse rank
9n for every n>=2. It retains the state-zero pivots through the
degeneration and the actual moving conic coordinates. This is an audited
paper proof, conditional on the established binary results, not a Lean
proof or a proof of the remaining CT8 determinant.

An independent Astra reviewer checked CT1–CT8, including ordinary-residue
signs, endpoint coefficients, interpolation, all block dimensions and both
old-node corrections. The determinant identities refer to the explicitly
transformed and consistently ordered matrix. The existing binary parity
theorem applies for n>=2 with its stated common-rho hypotheses; the
one-block binary pair is directly independent.

## Exact finite first-jet checks

`exploration/source24_conic_transverse_jet.py` independently builds the
ordinary-y residues of the complete CT2 products over the prime 1000003,
using dual numbers in x. It keeps all old-pole rows, including state zero,
and computes the induced map L M'(0) R from full left and right kernels
of M(0). The saved JSON records the leading minors, kernels and correction
matrices. The scalar product recurrences are also checked at ordinary
effect points.

| alpha | n | Leading rank | Two-dimensional correction determinant |
|---|---:|---:|---:|
| (1,2,3) | 2 | 4 | 996628 |
| (1,2,3) | 4 | 10 | 563801 |
| (1,2,3) | 6 | 16 | 550300 |
| (1,2,4) | 2 | 4 | 0 |
| (1,2,4) | 4 | 10 | 209128 |
| (1,2,4) | 6 | 16 | 86837 |

Both n=3 fixtures have full leading rank 9. Nonzero minors lift to
characteristic zero after clearing denominators. The modular zero in
the geometric n=2 fixture alone supplies no real upper bound; it also
must not be extrapolated to longer even lengths. The local run took
0.0441 seconds with maximum RSS 15,122,432 bytes and passed an independent
code audit. These finite checks corroborate the separate uniform proof;
they are not its induction bases.

## Append kernels without an invertible old source block

The following are exact paper reductions, not Lean results or
nonvanishing theorems for the complete source matrix. The first two
statements apply to general common-G tables, not just the conic family.
Assume the wide ambient geometry of
[SOURCE24_COMPLETION_QUOTIENT.md](SOURCE24_COMPLETION_QUOTIENT.md):
all table entries and determinants are nonzero, the denominator lines
are distinct, every line intersection has nonzero coordinates, no three
lines meet, and a matching coordinate-edge point lies on no other line.
Impose the same conditions after adding the suffix blocks. In particular,
every suffix kernel is regular and invertible at each earlier pair node.
All coefficient vectors and changes of basis below have parameter-only
constant entries; they do not depend on the effect variables.

For an old index \(\alpha=(t,s,a,b)\), \(t\ne s\), define the prefix,
raw completed row, and source row by
\[
 I_\alpha=\frac{A_t(a,b)X_aX_b}{L_{ta}}e_b,\qquad
 \widehat Q_\alpha=I_\alpha P_s^{\widehat t},\qquad
 F_\alpha=I_\alpha-\widehat Q_\alpha. \tag{CT9}
\]
The word \(P_s^{\widehat t}\) uses every old block except \(t\),
with \(s\) first and the others in increasing order. Extend these maps
linearly to an old coefficient vector \(y\). Write \(\rho_n\) for the
old cross-block double-residue map, in two independent zero-sum
coordinates at each node, and \(O_n=\rho_nF\). Since \(I(y)\) has only
single poles, \(\rho_n\widehat Q(y)=-O_ny\).

For \(i=(t,a)\), use the normalized single-line rows
\[
 V_{i,b}=\frac{A_t(a,b)X_aX_b}{L_i}e_b
                  -\delta_{ab}X_ae_a .
\]
They vanish at the coordinate vertices, and their line residues have
component \(b\) equal to \(A_t(a,b)X_aX_b\). The raw rows belong to
the wide ambient space obtained by adjoining the three diagonal
polynomials \(X_de_d\) to the completion space. Its residue-kernel
lemma therefore gives, for every \(y\in\ker O_n\), a unique expansion
\[
 \widehat Q(y)=\sum_{i,b}\kappa_{i,b}(y)V_{i,b}
                         +\sum_d d_d(y)X_de_d. \tag{CT10}
\]
Indeed, subtract the vertex values to enter the completion space and
apply (C2) of the completion note. Equivalently, after all pair
residues vanish, each line residue of
\(\widehat Q(y)\operatorname{diag}(X)^{-1}\) is a linear row
divisible by the matching \(X_a\). The displayed normalization then
fixes every \(\kappa_{i,b}\), and the remaining polynomial is diagonal.

Append a block \(N=n+1\) to every old word. Its actual interior source
row is
\[
 F^{[N]}(y)=I(y)-\widehat Q(y)K_N .
\]
At \(P=L_i=L_{Nc}=0\), the double residue for \(y\in\ker O_n\) is
\[
 \rho_{i,Nc}F^{[N]}(y)=
 -\kappa_{i,c}(y)A_t(a,c)X_a(P)X_c(P)v_{Nc}(P),
 \qquad i=(t,a), \tag{CT11}
\]
where \(v_{Nc}=(A_N(c,d)X_d)_d\). All prescribed geometric scalar
factors in (CT11) are nonzero under the assumptions. Old/old residues
are the old residues followed by right multiplication by \(K_N(P)\).
Consequently
\[
 \ker(\rho_{n+1}F^{[N]})
 =\{y\in\ker O_n:\kappa(y)=0\}
 =\{y:\widehat Q(y)\in
                    \operatorname{span}\{X_de_d:d=0,1,2\}\}. \tag{CT12}
\]
In particular, the longitudinal old-kernel map has exactly the rank
of \(\kappa|_{\ker O_n}\). Its rank is independent of the appended
time within the admissible geometry. This does not determine the rank
of the new incoming columns.

Appending two blocks gives a sharper kernel identity. Set
\(M=n+2\) and
\(F^{[N,M]}(y)=I(y)-\widehat Q(y)K_NK_M\). Then
\[
 \boxed{\quad
 \ker(\rho_{n+2}F^{[N,M]})=\ker\widehat Q .
 \quad} \tag{CT13}
\]
To prove the forward inclusion, old/old residues first imply
\(O_ny=0\), since the suffix \(K_NK_M\) is invertible there.
Old/\(N\) residues are (CT11) followed by the regular invertible
\(K_M\), so every \(\kappa_{i,c}\) vanishes. Thus
\(\widehat Q(y)=\sum_a d_aX_ae_a\). At the \(N,a\)/\(M,b\)
intersection the remaining residue is
\[
 -d_aX_a(P)A_N(a,b)X_b(P)v_{Mb}(P).
\]
It forces \(d_a=0\) for each \(a\). Conversely, if
\(\widehat Q(y)=0\), then \(F^{[N,M]}(y)=I(y)\) has no pair
residues. Hence the residue rank of this twice-appended interior
subfamily equals the rational-row rank of the old raw completed
family. The statement concerns only the old labels carried through
the suffix; it does not include the new boundary labels and does not
prove independence of the full enlarged family.

## A 27-square criterion for the singular conic three-to-four step

Now use three old conic blocks at a point where
\(\operatorname{rank}O_3=51\), and append a fourth admissible block.
Assume its complete outgoing transverse matrix \(P\) is invertible.
These assumptions hold on a nonempty generic parameter set by the
separate old-rank and transverse results. The old coefficient space
has dimension 54. Choose a 51-dimensional complement to its kernel
and use the three normalized combinations (C13) in
[SOURCE24_CONIC.md](SOURCE24_CONIC.md) as the kernel basis.

Order columns as the 51 old complement columns, the three old kernel
columns, the 27 outgoing columns, and the 27 incoming columns. Order
rows as 54 old/old coordinates, 27 transverse coordinates, and 27
longitudinal coordinates. The full 108-square residue matrix becomes
\[
 \begin{pmatrix}
 A_1&0&B&E\\
 0&0&P&Q\\
 C_1&C_{\ker}&R&S
 \end{pmatrix}. \tag{CT14}
\]
Here \(A_1\) has size \(54\) by \(51\) and full column rank.
All blocks use the same column normalizations and residue coordinates.
The 27-square block \(P\) is the complete outgoing block, not just
the \(9n-6\) controlled block \(H\) of (CT7).

The three-column longitudinal block \(C_{\ker}\) has full rank
without an old-source inverse. More explicitly, let \(h\) be the
nonzero scalar function (C12) of the conic note. Its kernel column
indexed by \(c\) has longitudinal entry
\[
 \sigma_i^c=\operatorname{Res}_{L_i}(h)(P_{i,4c})
                         X_c(P_{i,4c})
\]
in new-state sector \(c\), and zero in the other two sectors, by
(C14) there. Fix one old state-zero line \(i_0=(t,0)\). Each
\(\sigma_{i_0}^c\) is nonzero; their explicit pivots are (C15).
An explicit quotient map \(\Pi:\mathbb R^{27}\to\mathbb R^{24}\)
is therefore
\[
 (\Pi z)_{c,i}
    =z_{c,i}-\frac{\sigma_i^c}{\sigma_{i_0}^c}z_{c,i_0},
       \qquad i\ne i_0. \tag{CT15}
\]
There are eight retained rows per sector, and
\(\ker\Pi=\operatorname{im}C_{\ker}\).

Eliminate the outgoing columns using \(P\), retaining both cross
couplings:
\[
 Z=E-BP^{-1}Q,\qquad W=S-RP^{-1}Q.
\]
Choose any left inverse \(A_1^+\) of \(A_1\), and any full-row-rank
\(L:\mathbb R^{54}\to\mathbb R^3\) with
\(\ker L=\operatorname{im}A_1\). The full four-block pair-residue
matrix is invertible if and only if
\[
 \boxed{\quad
 {\cal H}_{3\to4}=
 \begin{pmatrix}
 LZ\\
 \Pi\bigl(W-C_1A_1^+Z\bigr)
 \end{pmatrix}
 \quad\hbox{is invertible.}\quad} \tag{CT16}
\]
This is a 27-square matrix: three old-cokernel rows and 24
longitudinal quotient rows.

For the equivalence, after eliminating \(P\) a relation with incoming
coefficient vector \(x\) must satisfy
\(A_1u+Zx=0\). This is solvable exactly when \(LZx=0\), in which
case \(u=-A_1^+Zx\). Its longitudinal equation is then solvable for
the three old-kernel coefficients exactly when
\(\Pi(W-C_1A_1^+Z)x=0\). If \(x=0\), full column rank of
\(A_1\) and \(C_{\ker}\) forces every remaining coefficient to
vanish. Thus the two kernels are isomorphic.

The criterion does not depend on the auxiliary choices. If a left
inverse is changed, its difference annihilates \(A_1\) and factors
as \(ML\). The lower block in (CT16) changes by
\(-\Pi C_1M\) times the upper block. Changing \(L\) or \(\Pi\)
only changes bases in their quotient spaces; changing the old
complement preserves the kernel characterization just proved.
Left inverses and quotient maps may be chosen rationally from any
nonzero parameter minor, so no effect-dependent coefficient operations
are involved.

Formula (CT16) avoids the nonexistent \(O_3^{-1}\). It retains the
old-node term \(C_1A_1^+Z\), the outgoing-to-old correction
\(BP^{-1}Q\), and the incoming longitudinal correction \(RP^{-1}Q\).
It is a conditional criterion, not a proof that its determinant is
nonzero, and it supplies no uniform conclusion for the remaining
regular block.

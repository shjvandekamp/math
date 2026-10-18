# Outgoing pole pivots and the remaining zero-diagonal block

**Status: audited paper results; not Lean formalized.** The
[Pro17 investigation](https://chatgpt.com/c/6ad152f7-dae0-83ed-aa55-920e68e46fa9)
proposed the reduction and the asymptotic outgoing pivot. Local review
checked the exact basis change, the sector vanishings, the moving-node
orders, and the two interpolation arguments proving the pivot is
generically nonzero. The determinant of the remaining block is not
proved generically nonzero for all lengths.

Use the actual raw append family and observation conventions of
[SOURCE24_RAW_QUOTIENT.md](SOURCE24_RAW_QUOTIENT.md). There are q old
blocks, with \(q\ge2\), and a new block N. Write
\(K_t=\operatorname{diag}(L_t)^{-1}A_t\operatorname{diag}(X)\).
All matrices have a common G and independent positive time factors.
The usual invertibility and line nonincidence conditions are assumed
where the rational observations are evaluated.

## Exact source basis and retained square observations

Let \(P_t\) be the full old word with t first and all remaining blocks
in increasing order. Let \(P^{\widehat t}\) be the increasing old
word omitting t. The outgoing and incoming raw completed rows are

\[
 \mathcal O_t^{cb}=X_cK_N(c,b)e_bP_t,\qquad
 \mathcal I_t^{ac}=X_aK_t(a,c)e_cK_NP^{\widehat t}.
 \tag{OP1}
\]

For \(t<q\), put

\[
 D_t^{cb}=\mathcal O_t^{cb}-\mathcal O_q^{cb},\qquad
 V_c=\sum_b\mathcal O_q^{cb},\qquad
 W_c=(V_c,\ (\mathcal I_t^{ac})_{t,a}),\qquad
 C_{ck}=\mathcal O_q^{ck}\quad(k=1,2).
 \tag{OP2}
\]

There are six C columns, \(9(q-1)\) D columns, and \(9q+3\) W
columns. This is an invertible constant change of the formal source
basis: \(\mathcal O_q^{c0}=V_c-C_{c1}-C_{c2}\), and each earlier
outgoing column is its D difference plus its q counterpart. Its
determinant is a sign, independent of effect and model parameters.

For each new line, take the two row-sum residue coefficients in the
basis \(A_N(c,1)X_1,A_N(c,2)X_2\) on \(L_{Nc}=0\). Denote these
six normalized observations by S. Then

\[
 S(C)=I_6,\qquad S(D)=0,\qquad S(W)=0.
 \tag{OP3}
\]

Indeed, the outgoing row sum is \(X_cK_N(c,b)\), independent of t;
the row sum of \(V_c\) is \(X_c\); and every incoming row sum
\(X_aK_t(a,c)\) has only old poles.

Let \(\Pi\) retain the new/old pole observations at old blocks
\(1,\ldots,q-1\), omitting all nine observations at old block q.
For a raw row H these are scalar coordinates of the double residues
of \(HK_N^{-1}\) on the new lines. Let \(\mathcal E\) consist of
all \(3q\) original matching observations and all \(6q+3\) original
axis observations. Thus \([S;\Pi;\mathcal E]\) is a square list
of \(18q\) observations on the \(18q\) boundary columns.

Set \(M=\Pi(D)\). It has size \(9(q-1)\) and is block diagonal
in the new sector c, because the columns in sector c have no new-line
pole in any other sector. When M is invertible, define

\[
 T=\mathcal E(W)-\mathcal E(D)M^{-1}\Pi(W).
 \tag{OP4}
\]

The retained square matrix in the basis (C,D,W) is exactly

\[
 \begin{pmatrix}
 I_6&0&0\\
 \Pi(C)&M&\Pi(W)\\
 \mathcal E(C)&\mathcal E(D)&\mathcal E(W)
 \end{pmatrix},\qquad
 \det=\det M\det T.
 \tag{OP5}
\]

This is a selected square minor of the full raw quotient observations.
Omitting the old-q pole rows is not a claim that they vanish or are
redundant on every raw row.

For comparison, eliminate S first and then an invertible matching
pivot J of size \(3q\), using the same retained observations. Its
remaining matching Schur matrix \(R_I\) has size \(15q-6\), whereas
T has size \(9q+3\). The two factorizations give

\[
 \det R_I=\pm\frac{\det M}{\det J}\det T.
 \tag{OP6}
\]

The sign depends only on the chosen row and column orders. Row
normalizations must be the same on both sides. In particular the
matching part of (OP4) is
\(\eta(W)-\eta(D)M^{-1}\Pi(W)\); the second term must not be
discarded merely because a matching pivot was available earlier.

## Exact sector vanishing and zero diagonal blocks

Let \(\mathcal H_c\) be the span of all outgoing and incoming raw
columns in new sector c. Group the rows of \(\mathcal E\) as
\(\mathcal E_c\): the q matching rows \(\eta_{tc}\), together
with the \(2q+1\) original axis observations on \(X_c=0\).
Then

\[
 \mathcal E_c(\mathcal H_c)=0.
 \tag{OP7}
\]

Here it is useful to cancel final-coordinate factors before evaluating
axes. Put \(J_t=\operatorname{diag}(X/L_t)A_t\). For
\(B=H\operatorname{diag}(X)^{-1}\), the raw formulas give

\[
 \begin{split}
 B(\mathcal O_t^{cb})
   &=\frac{X_cA_N(c,b)}{L_{Nc}}e_bJ_{P_t},\\
 B(\mathcal I_t^{ac})
   &=\frac{X_aA_t(a,c)}{L_{ta}}e_cJ_NJ_{P^{\widehat t}}.
 \end{split} \tag{OP8}
\]

The first row has its explicit \(X_c\), and the second has \(X_c\)
in row c of \(J_N\). Hence \(BA_N^{-1}\) vanishes on the entire
axis \(X_c=0\), proving the axis part of (OP7).

For a matching old pole \(L_{sc}\), taking its residue supplies a
second \(X_c\): the residue of an old conjugated kernel in state c
contains that factor. In the incoming exception \(s=t,a=c\), the
explicit \(X_a\) supplies it instead; if \(s=t,a\ne c\), there
is no such pole. Therefore
\((\operatorname{Res}_{L_{sc}}B)/X_c\) still vanishes at the
matching point \(L_{sc}=X_c=0\). Multiplication by \(A_N^{-1}\)
and selection of component c prove the matching part of (OP7).
The nonincidence assumptions exclude other poles at these points.

The correction \(DM^{-1}\Pi(W_c)\) stays in \(\mathcal H_c\).
Each column block \(W_c\) and row block \(\mathcal E_c\) has size
\(3q+1\). Thus T has the exact pattern

\[
 T=\begin{pmatrix}0&A&B\\ C&0&D\\ E&F&0\end{pmatrix}.
 \tag{OP9}
\]

This does not imply that any off-diagonal block is invertible. If A,D,E
are invertible, one may additionally factor

\[
 \det T=\det A\det D\det E\,
     \det\bigl(I+D^{-1}CE^{-1}FA^{-1}B\bigr).
 \tag{OP10}
\]

For example, multiply by the inverse of the block cycle with nonzero
blocks A,D,E, then eliminate its two remaining off-diagonal blocks.
The three-cycle has positive permutation sign. Formula (OP10) remains
conditional on the three stated inverses.

An important limit on further simplifications is that \(\Pi\) removed
only the old blocks before q. New-line poles supported at old block q
can remain. The original \(2q+1\) axis observations therefore cannot
be replaced by a reconstruction of the entire axis rational function
using only its old poles. Such a replacement would omit possible new
poles and could create false row relations. The zero diagonal in
(OP9) follows from the sector factor in (OP8), not from that replacement.

## Uniform nonvanishing of the outgoing pole pivot

The square pivot M is generically invertible for every \(q\ge2\).
This statement has a common-G witness and does not assume T is
invertible. For the witness let the unnormalized G have diagonal entries
one and off-diagonal entries \(\varepsilon\). Set the new time vector
to \((1,1,1)\), fix the last two old vectors as

\[
 f_{q-1}=(1,2,3),\qquad f_q=(1,4,5),
 \tag{OP11}
\]

and choose the earlier positive time vectors generically. The charts
below use definite projective representatives, so the valuation
statements refer to those representatives and to the specified scalar
coordinates of \(\Pi\). Other nonzero row normalizations preserve
nonvanishing but may change valuations.

Fix a new state c, and call the other states i,j. Order old pole rows
by state \((c,i,j)\), and outgoing D columns by outcome \((c,i,j)\).
Each group has \(q-1\) entries. Direct expansion at the moving nodes
gives the following lower bounds on entry orders:

\[
 M_c=\begin{pmatrix}
 O(\varepsilon^3)&O(\varepsilon^5)&O(\varepsilon^5)\\
 O(\varepsilon^4)&O(\varepsilon^6)&O(\varepsilon^5)\\
 O(\varepsilon^4)&O(\varepsilon^5)&O(\varepsilon^6)
 \end{pmatrix}.
 \tag{OP12}
\]

These bounds retain the prescribed move-t-first word order. In the
same-state chart below, the two other states are absorbing at order
zero. Their order-\(\varepsilon\) transitions are single flips, whose
sum is independent of the word order; consequently the difference of
two complete words starting in either of those states is
\(O(\varepsilon^2)\). For a word starting in c, its leading c
component is the product of the scalar c-retentions, also independent
of the order. The outgoing residue prefactors are all
\(O(\varepsilon^2)\), and taking the old-line residue supplies one
more \(\varepsilon\). The selected component of \(K_N^{-1}\) is
bounded in this chart. This gives the first row of (OP12).

In the different-state chart (OP18), use the zero-sum directions
\((e_a-e_b,e_c-e_b)\). The word differences starting in c, a, b
have respective component orders
\((\varepsilon,\varepsilon^2)\),
\((\varepsilon^2,\varepsilon)\), and
\((\varepsilon^2,\varepsilon^2)\). At order zero, a and c only
retain their own state or enter absorbing b. A return between a and c
costs two transitions of order \(\varepsilon\); the first b-to-a
contribution is the one-visit sum \(\Theta\) in (OP19). The outgoing
prefactors in starting-state order c,a,b have orders
\(\varepsilon^2,\varepsilon^3,\varepsilon^2\). Combining the
old-line factor \(\varepsilon\) with the inverse-kernel weights
\(O(1),O(\varepsilon)\) from (OP20) gives orders
\(\varepsilon^4,\varepsilon^6,\varepsilon^5\); exchanging a and b
gives the last row of (OP12). In all these residue computations the
exact moving old-line factor is canceled before its node is evaluated.
The other factored pole denominators are units at the limiting selected
node under the stated generic distinctness conditions.

After dividing the three column groups by
\(\varepsilon^3,\varepsilon^5,\varepsilon^5\), respectively, the
limit has form

\[
 \begin{pmatrix}
 A_c&*&*\\0&0&B_{ci}\\0&B_{cj}&0
 \end{pmatrix}.
 \tag{OP13}
\]

The three displayed pivot blocks are invertible generically. Their
interpolation proofs follow; nonzero regular row factors from the
residue charts are kept when deriving (OP12), and do not affect these
rank statements.

### Same-state nodes

For an old state-c pole use
\(X_i=x,X_j=y,X_c=-\varepsilon(x+y)\), with \(x+y=1\), and put

\[
 \Delta_t=(f_{ti}-f_{tc})x+(f_{tj}-f_{tc})y.
 \tag{OP14}
\]

The old node is \(\Delta_u=0\). The limiting old kernel fixes i,j
and has state-c row \((a_t,b_t,1-a_t-b_t)\) in order \((c,i,j)\),
where
\(a_t=-f_{tc}(x+y)/\Delta_t\), \(b_t=f_{ti}x/\Delta_t\).
Let \(v_t\) be the c-to-i entry of the actual move-t-first product.
Up to its fixed nonzero residue factors, the leading block is

\[
 A_c[u,t]=\left.\Delta_u(v_t-v_q)\right|_{\Delta_u=0},
 \qquad u,t<q.
 \tag{OP15}
\]

For the increasing prefix \(1,\ldots,t-1\), let
\(A_{t-1}=\prod_{s<t}a_s\), and let \(B_{t-1}\) be its c-to-i
entry. Then

\[
 h_t=v_t-v_1=(a_t-1)B_{t-1}+(1-A_{t-1})b_t.
 \tag{OP16}
\]

It uses only poles \(\Delta_1,\ldots,\Delta_t\). Its own-pole
coefficient is
\(-f_{tc}(x+y)B_{t-1}+(1-A_{t-1})f_{ti}x\), and is generically
nonzero. To see this, make every prefix kernel but one an identity
limit by sending both other-state time ratios to zero. With the one
active prefix block s, (OP16) reduces to

\[
 h_t=\frac{xy(f_{ti}f_{sj}-f_{tj}f_{si})}{\Delta_s\Delta_t}.
 \tag{OP17}
\]

This sign corresponds to \(v_t-v_1\). Only nonvanishing is needed.
For the final step the two fixed vectors (OP11) have active-coordinate
minors \(-2,2,2\) for the three choices of c. Earlier steps use
generic preceding vectors. Thus every needed own-pole coefficient is
a nonzero rational function in the allowed common parameters.

The functions \(h_2,\ldots,h_q\) are independent by their nested own
poles. They all vanish at x equal to zero and at y equal to zero, so
they span the \((q-1)\)-dimensional space
\(xy\,p_{q-2}(x,y)/\prod_s\Delta_s\), where p is homogeneous of
degree \(q-2\). The functions \(v_t-v_q\), \(t<q\), are another
constant basis of that space. Taking residues at its first \(q-1\)
distinct poles is injective: a numerator of degree \(q-2\) cannot
vanish at those \(q-1\) points unless it is zero. This proves (OP15)
invertible. The fixed chosen output coordinate of the stripped residue
is i in this same-state chart.

### Different-state nodes

For old state \(a\ne c\), let b be the third state. Use the exact
moving chart

\[
 X_b=1,\quad X_a=\varepsilon z,\quad
 X_c=-\varepsilon(1+\varepsilon z),\quad
 z_u(\varepsilon)=-\frac{f_{ub}-\varepsilon f_{uc}}
                            {f_{ua}-\varepsilon^2f_{uc}},\quad
 r_s=f_{sb}/f_{sa}.
 \tag{OP18}
\]

Thus \(z_u(0)=-r_u\). Choose component a of the stripped residue.
The limiting state-a retention is \(\tau_s=z/(z+r_s)\), and the
first state-b to state-a entry is \(\varepsilon^2 z/r_s\).
For a prescribed old word define

\[
 \Theta_{\rm word}(z)=\sum_s\frac z{r_s}
                    \prod_{\text{blocks after }s}\tau_j,
 \qquad \mathcal T(z)=\prod_s\tau_s,
 \qquad \mathscr H_t(1/z)=
       \frac{\Theta_{P_t}(z)-\Theta_{P_q}(z)}{\mathcal T(z)}.
 \tag{OP19}
\]

The nonzero block in (OP13) is, up to the fixed ordering of i,j,
\[
 B_{ca}[u,t]=\rho_u\,\mathscr H_t(-1/r_u),\qquad
 \rho_u=-f_{ua}\frac{z_u+1}{z_u}
              \frac{z_u^q}{\prod_{s\ne u}(z_u+r_s)},\quad z_u=-r_u,
 \tag{OP20}
\]
where the argument of \(\mathscr H\) is the variable \(w=1/z\).
The factors \(\rho_u\) are nonzero generically. The moving chart and
the inverse new kernel are part of this calculation: on the selected
component, \((e_a-e_b)K_N^{-1}\) tends to \((z+1)/z\), whereas
\((e_c-e_b)K_N^{-1}\) has leading term
\(\varepsilon(z+1)\). Keeping those different orders is necessary
for (OP12).

There is an explicit determinant for the polynomial evaluations in
(OP20). Let \(S_j(w)=\prod_{s\le j}(1+r_sw)\), with \(S_0=1\).
Then

\[
 \Phi_{\rm word}=\Theta_{\rm word}/\mathcal T
       =\sum_s\left(1+\frac1{r_sw}\right)
                    \prod_{\text{blocks before }s}(1+r_jw),
\]
and the move-t-first difference from the increasing word is
\[
 E_t=\Phi_{P_t}-\Phi_{P_1}
   =\sum_{j<t}\left\{
       (r_t/r_j-1)S_j+(1-r_j/r_t)S_{j-1}\right\}.
 \tag{OP21}
\]

It has degree \(t-1\), with leading Newton coefficient
\((r_t-r_{t-1})/r_{t-1}\). Define the linear functional on the
Newton basis through degree \(q-1\) by
\(\Lambda S_{2k}=1\) and
\(\Lambda S_{2k-1}=-r_{2k-1}/r_{2k}\).
Odd and even terms in (OP21) cancel in pairs; when t is even the last
unpaired term also vanishes because its partner parameter is \(r_t\).
Thus \(E_2,\ldots,E_q\) form a basis of \(\ker\Lambda\).

Evaluation at \(-1/r_1,\ldots,-1/r_{q-1}\) has kernel spanned by
\(S_{q-1}\). Its \(\Lambda\) value is
\(\chi_q=1\) for odd q and \(\chi_q=-r_{q-1}/r_q\) for even q,
which is nonzero. More precisely, with \(\mathscr H_t=E_t-E_q\)
and \(E_1=0\),

\[
 \det\bigl(\mathscr H_t(-1/r_u)\bigr)_{u,t<q}
 =\chi_q\prod_{t=2}^q\frac{r_t-r_{t-1}}{r_{t-1}}
       \prod_{1\le j<u\le q-1}(1-r_j/r_u).
 \tag{OP22}
\]

The Newton evaluation determinant supplies the last product. The
coefficient minor of \(E_2,\ldots,E_q\) supplies
\((-1)^{q-1}\chi_q\) times the first product; changing that basis
to \(E_1-E_q,\ldots,E_{q-1}-E_q\) supplies a second
\((-1)^{q-1}\). This verifies the sign in (OP22). The last two fixed
time vectors have distinct r values in each different-state sector;
the earlier vectors can be chosen generically. Hence both B blocks
in every sector are invertible.

### Common-parameter conclusion and normalization

All nine leading blocks in (OP13) have nonzero determinant on the same
irreducible family with the last two times fixed as in (OP11). Their
finitely many nonzero open conditions can be intersected with positive
earlier times and the required node geometry. It follows that, in the
specified projective charts and scalar coordinates,

\[
 \det M=\varepsilon^{39(q-1)}(c+O(\varepsilon)),\qquad c\ne0.
 \tag{OP23}
\]

To restore the first-column-one convention, multiply the rows of G by
\(\operatorname{diag}(1,\varepsilon^{-1},\varepsilon^{-1})\).
This leaves every kernel and raw source row unchanged, and also leaves
the matching observations unchanged: their old-line and inverse-new-row
scalings cancel. A \(\Pi\) row indexed by new c and old a gains
the factor \(g_cg_a\), where \(g=(1,\varepsilon^{-1},\varepsilon^{-1})\).
The total determinant factor is \(\varepsilon^{-12(q-1)}\). Thus
the same-chart normalized pivot has valuation \(27(q-1)\).
The powers 39 and 27 are chart-dependent; the nonzero common-G minor
is the invariant conclusion.

For every q this proves the outgoing pole pivot required in (OP4).
It reduces the retained-square nonvanishing problem to \(\det T\),
with the exact zero-diagonal structure (OP9). Neither that structure
nor the conditional cycle formula proves \(\det T\ne0\) uniformly.
No full raw-boundary or all-length source independence conclusion is
asserted here.

## Independently reconstructed finite certificates

The accepted external exact verifier
[source24_outgoing_pole_reduction.py](../exploration/source24_outgoing_pole_reduction.py)
and its
[saved results](../exploration/source24-outgoing-pole-reduction-results.json)
give the following nonzero determinants modulo 1,000,003. These are
finite witnesses, separate from the uniform proof of M above.

| q | size M | det M | size T | det T |
|---|---:|---:|---:|---:|
| 2 | 9 | 343131 | 21 | 30554 |
| 3 | 18 | 50168 | 30 | 210275 |
| 4 | 27 | 839092 | 39 | 530412 |
| 5 | 36 | 667130 | 48 | 594044 |
| 6 | 45 | 568248 | 57 | 760966 |

The verifier checks all three diagonal blocks of T vanish, and checks
the determinant factorization both against the independently assembled
original square and against the saved matching-pivot determinant. Its
fixed permutations give the minus sign in (OP6). At q=2, actual kernel
products independently check 1,944 double-residue components, 216
matching-jet entries, and 108 ordinary components.

All six off-diagonal blocks have rank 5 of 7 at the q=2 fixture, so
(OP10) cannot be applied there. They are invertible at q=3,4,5,6,
with sizes 10,13,16,19; the corresponding cycle-factor determinants in
(OP10) are 137414, 18774, 933172, and 889705 modulo the same prime.
These checks do not supply a uniform proof of the remaining determinant.

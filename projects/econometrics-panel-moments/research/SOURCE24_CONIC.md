# A conic specialization, three exact relations, and finite ranks

**Status: audited paper identities and external exact certificates; not Lean
formalized.** Three explicit relations below prove a uniform three-block
residue-rank upper bound of 51. A saved nonzero minor makes that bound
generically sharp. No uniform nonvanishing theorem from four blocks onward
is proved here. The earlier
characteristic-zero rank-51 certificate for one three-block witness remains
in `exploration/conic_residue_nullspace.py` and its saved JSON.

Choose positive distinct state parameters \(\alpha_0<\alpha_1<\alpha_2\),
\(G_{ab}=\alpha_a^b\), and
\(A_t=G\operatorname{diag}(1,b_t,b_t^2)\). Write
\(q_{ta}=\alpha_ab_t\), requiring all these numbers to be distinct.
Every denominator line has the form

\[
 L(q)=X_0+qX_1+q^2X_2.
\]

For two different parameters \(x,y\), their intersection and every
remaining line evaluation are explicitly

\[
 P_{xy}=(xy,-x-y,1),\qquad L(z)(P_{xy})=(z-x)(z-y).
 \tag{C1}
\]

Thus all pair coordinates are nonzero and no three lines meet, including
same-block pairs. The common matrix is invertible. These facts do not imply
source independence or positivity of transition entries at the pair points:
the middle numerator coordinate is negative.

The new `exploration/source24_conic.py` evaluates actual ordered source
products using (C1), retaining the first two raw residue components. It
compares every entry with the existing residue-matrix implementation.
Since the cross-product representative is \((y-x)P_{xy}\), a cubic
double residue in its degree-one residue-vector basis acquires the factor
\((y-x)^2\); the comparison explicitly removes this factor.

The saved `exploration/source24-conic-results.json` records exact ranks
modulo 1,000,003:

| State parameters | Time parameters | Blocks | Rank / size |
|---|---|---:|---:|
| (1, 2, 3) | (2, 5) | 2 | 18 / 18 |
| (1, 2, 3) | (2, 5, 11) | 3 | 51 / 54 |
| (1, 2, 3) | (2, 5, 11, 23) | 4 | 108 / 108 |
| (1, 2, 3) | (2, 5, 11, 23, 47) | 5 | 180 / 180 |
| (1, 2, 4) | (8, 64, 512) | 3 | 51 / 54 |
| (2, 5, 9) | (2, 7, 19) | 3 | 51 / 54 |

The full square minors at four and five blocks prove nonvanishing over
characteristic zero at those rational fixtures, since every denominator
in the computation is a unit modulo the recorded prime. The deficient
modular ranks do not themselves prove characteristic-zero upper bounds.
The fifth row is a global time rescaling of the previously certified
three-block economic witness, not the identical coefficient table.

The final run, including the restricted-column diagnostics below, took
0.604 seconds and 17,596,416 bytes maximum RSS. An independent
Astra researcher reviewed the code, ordering, pole removal, and coordinate
conversion; no Lean theorem is asserted.

## An audited three-block reduction

At three blocks, restrict the coefficients of the actual source rows to
shared and divergent states \(a,b\in\{0,2\}\), giving 24 columns.
For an unordered pair of blocks \(t,r\), let \(s\) be the remaining
block and set

\[
 H_{ab}=c_{t,r,a,b}A_t(a,b)A_r(b,1)
       +c_{r,t,b,a}A_t(a,1)A_r(b,a). \tag{C2}
\]

At \(L_{ta}=L_{s1}=0\), the actual combined source residue is
\(-X_aX_1v_{s1}\sum_b X_bH_{ab}/L_{rb}\). At
\(L_{rb}=L_{s1}=0\), it is
\(-X_bX_1v_{s1}\sum_a X_aH_{ab}/L_{ta}\).
State one can only occur in the last block of these three-transition
products, so no other permitted source column contributes at these pairs.
Pairs whose two marked states are both one have zero residue.

Write \(x_a=q_{ta}\), \(y_b=q_{rb}\), \(z=q_{s1}\), and

\[
 R_a=\frac{x_az(y_2-x_a)(y_2-z)}{(y_0-x_a)(y_0-z)},\qquad
 C_b=\frac{y_bz(x_2-y_b)(x_2-z)}{(x_0-y_b)(x_0-z)}. \tag{C3}
\]

The four vanishing conditions are \(H_{a2}=-R_aH_{a0}\) and
\(H_{2b}=-C_bH_{0b}\). Their compatibility ratio simplifies to

\[
 \frac{R_2C_0}{R_0C_2}=\frac{x_2y_0}{x_0y_2}=1. \tag{C4}
\]

The last equality uses the common ratio \(\alpha_2/\alpha_0\).
Consequently these four equations have rank exactly three, with kernel
proportional to
\(\left(\begin{smallmatrix}1&-R_0\\-C_0&R_2C_0\end{smallmatrix}\right)\).
Since each four-entry \(H\) is a surjective image of eight source
coefficients, cancelling all mixed state-one residues leaves dimension
15 inside this 24-column subfamily. An independent Astra reviewer checked
the actual residue formulas, compatibility ratio, and generic assumptions.
The remaining extreme-state pairs are not settled by this count.

The smaller choice \(H=0\) is particularly concrete. For every
unordered block pair and \(a,b\in\{0,2\}\), take the source combination

\[
 \frac{F_{t,r,a,b}}{A_t(a,b)A_r(b,1)}
 -\frac{F_{r,t,b,a}}{A_t(a,1)A_r(b,a)}. \tag{C5}
\]

These 12 coefficient columns are independent before applying the residue
map, and all their mixed state-one residues vanish. The new script records
rank 21 for the 24-column restriction, and rank 9 for (C5), in each of the
three three-block conic fixtures above. Thus each tested nullspace is
already carried by (C5). These finite ranks motivated the parameter
identities proved next; the ranks alone do not supply an upper bound.

## Three explicit parameter identities at three blocks

Put \(p_t=\alpha_0b_t\), \(k=\alpha_2/\alpha_0>1\), and
\(\Pi=p_1p_2p_3\). Let \(\epsilon_{tsr}\) be the sign of the
permutation \((t,s,r)\) of \((1,2,3)\). For each order, define three
unsigned coefficient rows, supported on \((a,b)=(0,0),(0,2),(2,0),(2,2)\):

\[
 c^{(1)}_{ts}=(-p_t,\ p_r,\ k\Pi,\ -p_sp_r^2),\qquad
 c^{(2)}_{ts}=(p_t/p_r,\ -k,\ -k^2p_tp_s,\ k^2p_sp_r),
 \quad c^{(3)}_{ts,ab}=(q_{ta}+q_{sb})c^{(1)}_{ts,ab}. \tag{C6}
\]

Write \(R^{(j)}=\sum_{(t,s,r)\in S_3}\epsilon_{tsr}
\sum_{a,b}c^{(j)}_{ts,ab}F_{t,s,a,b}\). Then

\[
 R^{(1)}=R^{(2)}=0,\qquad
 R^{(3)}=\sum_{\mathrm{cyc}(t,s,r)}(p_r-p_s)
       (-p_tE_{t0}+k\Pi E_{t2}),\qquad
 E_{ta}=X_ae_a(I-K_t). \tag{C7}
\]

The two rational-zero identities were supplied by the user-authorized
[GPT-6 Pro investigation](https://chatgpt.com/c/6ad13166-7f64-83eb-bfdb-859beff098a0).
The primary researcher derived the third relation and its single-block
right side locally. An independent Astra researcher checked the ordered
path cancellation and independence argument. The proof below uses all six
actual orders; no transition matrices are commuted.

Separate each source into its prefix and completed term, so
\(R^{(j)}=S^{(j)}-T^{(j)}\). Set
\(\theta^{(j)}_{ts}(a,b)=c^{(j)}_{ts,ab}q_{ta}^{b-1}\).
For the first two families these two-by-two matrices are

\[
 \Theta^{(1)}_{ts}=\begin{pmatrix}-1&p_tp_r\\p_sp_r&-k\Pi p_r\end{pmatrix},
 \qquad
 \Theta^{(2)}_{ts}=\begin{pmatrix}1/p_r&-kp_t\\-kp_s&k^3\Pi\end{pmatrix}.
 \tag{C8}
\]

Both obey \(\theta_{st}(b,a)=\theta_{ts}(a,b)\), as does the third.
For a fixed assignment of states to the three blocks, put
\(Q_t=q_{t,a_t}\). Pairing orders \((t,s,r)\) and \((s,t,r)\)
in the completed path expansion leaves the coefficient

\[
 \theta_{ts}(a_t,a_s)
     (Q_tQ_s^{a_r}-Q_sQ_t^{a_r})Q_r^d. \tag{C9}
\]

The common denominator is \(\prod_tL_{t,a_t}\), and the common
effect factor is \(X_{a_1}X_{a_2}X_{a_3}X_d\). If a state is one,
it must occur last, and the parenthesis in (C9) is zero. More than one
state one leaves no permitted term. For endpoint states write
\(a_t=2I_t\), \(I_t\in\{0,1\}\), and \(N=I_1+I_2+I_3\).
Direct substitution in (C8) gives common cyclic factors

\[
 W_1=-(-1)^N k^{I_1I_2+I_1I_3+I_2I_3}
              \frac{\Pi^N}{\prod_t p_t^{I_t}},\qquad
 W_2=-k^N W_1.
\]

The respective cyclic sums of (C9) are therefore

\[
 W_1\sum_{\mathrm{cyc}}(Q_t-Q_s)Q_r^d,\qquad
 W_2\sum_{\mathrm{cyc}}(Q_t-Q_s)Q_r^{d-1},\qquad
 W_1\sum_{\mathrm{cyc}}(Q_t^2-Q_s^2)Q_r^d. \tag{C10}
\]

The first vanishes for \(d=0,1\); the second for \(d=1,2\); and
the third for \(d=0,2\). These are scalar telescoping identities.
Thus the three completed sums have only output 2, 0, and 1, respectively.
For the first prefix sum, output zero cancels when \(s,r\) are
exchanged; for the second, output two cancels the same way. No prefix
has output one. Since every transition has row sum one,
\(S^{(j)}\mathbf1=T^{(j)}\mathbf1\), proving the first two
identities in (C7).

For the third, components zero and two of \(R^{(3)}\) equal those
of its prefix. Grouping the two orders for each fixed \(t\) gives

\[
 R^{(3)}_0=\sum_{\mathrm{cyc}}(p_r-p_s)
  \left(\frac{p_tX_0^2}{L_{t0}}-\frac{k\Pi X_0X_2}{L_{t2}}\right),
\quad
 R^{(3)}_2=\sum_{\mathrm{cyc}}(p_r-p_s)
  \left(\frac{p_t^3X_0X_2}{L_{t0}}-
        \frac{k^3\Pi p_t^2X_2^2}{L_{t2}}\right). \tag{C11}
\]

These are exactly the corresponding components of the right side of
(C7). The polynomial terms cancel by
\(\sum_{\mathrm{cyc}}p_t(p_r-p_s)=0\) and
\(\sum_{\mathrm{cyc}}(p_r-p_s)=0\). Row sum zero supplies the
remaining component. The right side of (C7) is nonzero: its coefficients
on the distinct-line single-block rows are nonzero, and those rows are
independent by their individual line residues.

All three coefficient vectors lie in the kernel of the double-residue
map. The first two are independent: their two-column coefficient minor
on \(F_{1,2,0,2},F_{1,3,0,2}\) is \(k(p_3-p_2)\ne0\).
The third is outside their span because its rational row is nonzero.
Alternatively, the three coefficient rows \((t,s,0,0),(t,s,0,2),
(t,s,2,0)\), for a positive cyclic order, give determinant
\(kp_t^2p_sp_r(k-1)^2(p_t-p_s)\ne0\).

Consequently \(\operatorname{rank}O_3\le51\) throughout this conic
family. The saved nonzero 51-minor proves that its generic rank is exactly
51. At a generic conic point the 54 shared rational rows themselves have
rank 52: two exact zero relations give the upper bound, while the residue
rank 51 plus the nonzero single-pole row (C7) gives the lower bound.
These statements are paper proofs supported by external exact arithmetic,
not additions to the Lean theorem list.

The bounded `exploration/source24_conic_relations.py` independently checks
all 162 required ordered-path zero identities as exact Laurent polynomials
over the integers, covering all 27 state assignments, and 45 prefix support
identities. It also checks the actual residue products at all three saved
three-block conic fixtures, coefficient rank three, and direct ordinary
evaluations of the two zero rows and the nonzero single-pole row. The primary
researcher reviewed the implementation. These checks do not replace the
paper argument or constitute Lean verification.

## Appending a block separates the three missing residue directions

Write d_t=p_r−p_s for each positive cyclic order and set

\[
 h=\sum_{\mathrm{cyc}(t,s,r)}d_t
       \left(\frac{p_t^2X_0}{L_{t0}}
             -\frac{k^2p_t\Pi X_2}{L_{t2}}\right). \tag{C12}
\]

The prefix and completed calculations above give
T1=S1=h X2 e2 and T2=S2=−h X0 e0/Pi. For the third,
C11 implies S3·1=−h X1, after cancelling the same two polynomial
cyclic sums used in C7. Hence T3=−h X1 e1. The rational function h
is nonzero: its residue at L_t0 is d_t p_t² X0.

Append a fourth block K4. For interior labels the actual source identity is
F^(4)=F^(3)K4+I_prefix(I−K4). Let G_j denote the three combinations
with the unchanged constant coefficient vectors C6. Normalize them as
C0=Pi G2, C1=G3, C2=−G1. Then

\[
 C_0=hX_0e_0(K_4-I),\qquad
 C_1=R^{(3)}+hX_1e_1(K_4-I),\qquad
 C_2=hX_2e_2(K_4-I). \tag{C13}
\]

The extra R3 term has only old single poles. At an old/new intersection
(i,(4,j)), the double residue of column C_c is therefore

\[
 \delta_{cj}\,\operatorname{Res}_{L_i}(h)X_jv_{4j}. \tag{C14}
\]

Fix any old state-zero line L_t0. Its h residue is nonzero at all three
admissible crossings with new lines, and the three columns in C14 have
disjoint new-state support. Thus these three terminal profiles are
independent. For a conic fourth block, write z_j=q_4j and use
P_j=(p_t z_j,−p_t−z_j,1). In the new numerator-vector coordinate, the
three diagonal pivots are

\[
 d_t p_t^4z_0^2,\quad -d_t p_t^3z_1(p_t+z_1),\quad
 d_t p_t^3z_2;
 \qquad \det=-d_t^3p_t^{10}z_0^2z_1z_2(p_t+z_1)\ne0. \tag{C15}
\]

At a generic old conic point with rank O3=51, the old/old rows of the
appended 54-column subfamily are the original residues followed by right
multiplication by K4 at each node. These matrices are invertible and
preserve the zero-sum plane. Their coefficient kernel is exactly the
three C6 vectors, on which C14 is injective. Consequently the 54 interior
columns become independent after one admissible appended block. Further
appended blocks preserve this argument: old and first-appended pair
residues are multiplied by the invertible remaining suffix.

There is a separate consequence before appending. A relation among the
54 raw completed rows Qhat3 must lie in that same three-dimensional
residue kernel. Its three possible images are h X2 e2, −h X0 e0/Pi,
and −h X1 e1, which are independent. Thus those raw completed rows
already have rank 54 at a generic three-block conic point.

An independent Astra researcher derived C12–C15 and a separate reviewer
checked the signs, the extra R3 term, and both rank deductions. These
results concern the interior subfamily and raw completed rows. They do
not prove independence of the new boundary columns or the full enlarged
source family.

The remaining conic question is uniform nonvanishing for \(m\ge4\).
The three-block generic nonvanishing witness for the unrestricted common-G
family uses a perturbation off the conic. Thus the conic obstruction does
not refute the general equation-(24) target.

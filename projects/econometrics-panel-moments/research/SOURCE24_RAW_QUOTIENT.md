# Explicit raw append quotient and a uniform 18-column subfamily

**Status: independently audited paper results; not Lean formalized.** The
full 18q-column boundary rank remains open. The
[GPT-6 Pro investigation](https://chatgpt.com/c/6ad13a68-9e88-83ed-90ba-098f4f9795f8)
proposed these results; the primary researcher and an independent Astra
reviewer checked the quotient kernel, collision argument and witness.

Use the wide ambient Wwide_m of `SOURCE24_RAW_APPEND.md`, of dimension
9m²+3. Its rows have the final-coordinate factors, matching departure
factors, no same-block double residues, and zero-sum cross-pair residues.
Appending the new stochastic kernel K_N, N=q+1, preserves these
conditions and is injective over the rational-function field. Therefore

\[
 \dim(\widehat W_{q+1}/\widehat W_qK_N)=18q+9. \tag{RQ1}
\]

For any H in Wwide_(q+1) put

\[
 B=H\operatorname{diag}(X)^{-1},\quad C=BA_N^{-1},\quad
 R=HK_N^{-1}=C\operatorname{diag}(L_{N0},L_{N1},L_{N2}). \tag{RQ2}
\]

These expressions retain the actual ordered products when H is a source.

## Exact quotient coordinates

At each new/old intersection, with new state c, the double residue of R
has component c zero, because R_c contains L_Nc. Its row sum is zero,
because K_N^−1 1=1. Thus it has one scalar coordinate in the line
{z:z_c=0,sum z=0}. These supply 9q tests. On each new line also retain
the two coefficients of the homogeneous linear polynomial

\[
 \sigma_c=\left.\frac{L_{Nc}R\mathbf1}{X_c}\right|_{L_{Nc}=0}.
 \tag{RQ3}
\]

This is polynomial already on the whole ambient: row sums have no pair
poles, and their single-line residue contains X_c.

The 9q+6 tests vanish exactly when R has no new-line poles. To prove the
nontrivial direction, let r_c=(L_Nc R/X_c)|_L_Nc. Vanishing cross tests
remove its old-line poles; same-block double residues were already zero.
It is consequently a linear polynomial row with component c zero and
row sum zero, so r_c=ell_c(e_i−e_j), for the other two states i,j.
At L_Nc=L_Ni its component i vanishes, and at L_Nc=L_Nj its component j
vanishes, by R_i=C_i L_Ni and the absence of same-block double poles.
The two distinct zeros force the linear form ell_c to vanish.

Next, on each axis X_d=0 take the residues of C_d at its 2q old-line
points with departure state a!=d, and its value at one fixed ordinary
axis point. These 6q+3 functionals are globally defined, before imposing
the first tests. Their sufficiency uses the first tests: once R has no
new poles, C_d=R_d/L_Nd has no new poles on this axis. The possible
L_Nd pole is removed by its departure factor X_d. Old state-d residues
vanish there for the same reason. Therefore C_d restricted to the axis
has only those 2q poles, and residues plus one value determine it.
All these tests vanish exactly when every R_d has its required X_d factor.

Finally retain one matching value per old line:

\[
 \eta_{ta}(H)=
 \left[\left(\frac{\operatorname{Res}_{L_{ta}}B}{X_a}\right)
 A_N^{-1}\right]_a\bigg|_{L_{ta}=X_a=0}. \tag{RQ4}
\]

The quotient by X_a is regular at the matching point by the ambient
departure condition. Once the preceding tests vanish, for output d!=a
the old departure factor remains automatically after dividing R_d by X_d.
For output a, the remaining matching condition is precisely RQ4=0,
since its residue is the displayed coefficient times L_Na, nonzero at
that old matching point. All other ambient conditions are inherited.

Thus these 18q+9 linear functionals define a map T_N with

\[
 \ker T_N=\widehat W_qK_N,\qquad
 \widehat W_{q+1}/\widehat W_qK_N\simeq\mathbb K^{18q+9}. \tag{RQ5}
\]

The new-pole and axis groups alone have at most 15q+9 rows. On the
18q boundary coefficient space they leave at least 3q−9 directions for
q>=4. Hence the matching conditions RQ4, or equivalent information, are
essential to this sufficient ambient-quotient approach. This is not a
dependence result for the raw sources.

## Eighteen columns associated with one old block

Fix any old t. For every q>=2 the eighteen actual columns

\[
 \{\widehat Q_{N,t,a,b}:a,b=0,1,2\}\ \cup\
 \{\widehat Q_{t,N,a,b}:a,b=0,1,2\} \tag{RQ6}
\]

are generically independent modulo Wwide_q K_N. In fact stripped new-line
residues already separate them.

For a nonvanishing witness coalesce the old matrices to H=K(A), and put
r=q−1. On a new line L_Nc=0 set v=A_N(c,:)diag(X), so v1=0. Only
six of RQ6's columns contribute there. Write their outgoing coefficients
alpha_b and incoming coefficients beta_i, and put
ell=sum_i beta_i A(i,c)X_i/L_i. After removing the common X_c factor,
their residue before stripping is

\[
 (v\operatorname{diag}(\alpha)H+\ell v)H^r. \tag{RQ7}
\]

The left kernel of K_N^−1 on this line is span(v). Consequently no
stripped new pole means
\[
 v\operatorname{diag}(\alpha)H+\ell v=\lambda vH^{-r}.
\]
Taking row sums forces all alpha_b to equal one scalar kappa, because
sum_b alpha_b A_N(c,b)X_b vanishes identically on L_Nc.

On the two-dimensional zero-sum space set tau=tr(H)−1 and delta=det(H).
Define S0=0,S1=1,S_(j+1)=tau S_j−delta S_(j−1). Cayley–Hamilton gives

\[
 H^{-r}=\frac{-S_rH+S_{r+1}I}{\delta^r}
 \quad\hbox{on the zero-sum space}. \tag{RQ8}
\]

Generically v and vH are independent. If kappa!=0, comparison in that
basis implies

\[
 \ell/\kappa=-S_{r+1}/S_r=-\tau+\delta S_{r-1}/S_r. \tag{RQ9}
\]

At each of the three old-line intersections, tau has a nonzero simple
pole and delta has at most a simple pole. The recurrence shows S_r has
leading pole tau^(r−1); therefore delta S_(r−1)/S_r is regular there
(and is zero when r=1). Matching the three principal parts in RQ9
forces the particular function ell/kappa to be

\[
 -\sum_i A(i,i)X_i/L_i=-\operatorname{tr}H=-\tau-1. \tag{RQ10}
\]

There is no arbitrary constant in this step: each of the three Xi/Li has
its own nonzero pole, so its coefficient is fixed by that pole. RQ9–RQ10
would give delta S_(r−1)/S_r=−1. At an ordinary coordinate-axis point
on the new line, delta=0 and tau!=0, hence S_r=tau^(r−1)!=0. The
identity would read 0=−1. Thus kappa=0; comparing the H coefficient
in RQ8 then gives lambda=0, followed by ell=0 and all beta_i=0.
The three c sectors use disjoint coefficients, proving independence.

## A common positive witness and the collision limit

Use G with rows (1,2,7),(1,5,3),(1,11,13), old time factors (1,1),
and new factors (2,3). Its determinant is 54. The new line coefficients
(n1,n2) are (4,21),(10,9),(22,39). They avoid every old line and
coordinate-axis collision. Evaluating those new lines at the three old
pair nodes gives, up to nonzero representative scaling, the triples
(50,38,176), (38,−10,56), and (59,−7,23); none vanish.

At X2=0, X1=1, X0=−n1, all old denominators are nonzero and
tau=−3n1/((2−n1)(5−n1)) is nonzero. This supplies RQ10's contradiction.
At X1=X2=1, X0=−n1−n2, the scalar n2(vH)_1−n1(vH)_2 is nonzero
for all three sectors. For c=0 it is less than −3732; for c=1 it equals
−18506/110; for c=2 it is less than −214. These verified rational
calculations establish the required v,vH independence. The witness
conditions do not depend on r.

The old nodes coincide at this witness. Do not substitute it into the
9q node-coordinate matrix. Instead take finite ordinary-point evaluations
of the stripped new-line residue functions, avoiding the old poles and
coordinate axes. Their proved functional independence supplies a nonzero
evaluation minor. Its entries are regular in nearby old time factors,
so that minor stays nonzero after the old times split. At every split
fixture these residue evaluations annihilate the appended ambient, proving
the generic RQ6 statement with valid distinct-line geometry.

The unresolved sufficient induction condition is full rank 18q of T_N
on all 18q boundary columns. The uniform rank-18 subfamily does not give
that condition, and ranks from overlapping tests cannot simply be added.

## Uniform full rank of the incoming matching map

**Status: independently audited paper proof; not Lean formalized.**
For each fixed q>=2, the 3q functionals eta_(u,c) in RQ4 have generic
rank 3q on the 6q incoming raw columns

\[
 \{\widehat Q_{t,N,a,b}:1\le t\le q,\ a,b\in\{0,1,2\},\ b\ne a\}.
 \tag{RQ11}
\]

Here the old blocks are numbered 1,...,q. This is a statement about the
matching map on the entire subfamily RQ11. It does not assert that the
matching map has this rank on the joint kernel of the preceding new-pole
and axis tests.

### Restrict to the matching axes before coalescing

Fix the same positive coefficient matrix

\[
 A=G=\begin{pmatrix}1&2&7\\1&5&3\\1&11&13\end{pmatrix},\qquad
 A^{-1}=\frac1{54}
 \begin{pmatrix}32&51&-29\\-10&6&4\\6&-9&3\end{pmatrix}.
 \tag{RQ12}
\]

Coalesce the old time factors to (1,1), while allowing
A_N=A diag(d_0,d_1,d_2), with d_0=1. This collision is used only after
restricting the matching formulas to X_c=0. Before collision, row c of
every remaining conjugated old kernel J_j=diag(X/L_j)A_j is identically
zero on that axis. It therefore extends as a zero row when its
denominator also vanishes at collision. The active rows have nonzero
denominators at the following matching representatives:

\[
 Q_0=(0,7,-2),\qquad Q_1=(-3,0,1),\qquad Q_2=(-11,1,0).
 \tag{RQ13}
\]

For row state c, all expressions below are evaluated at Q_c. Let
\(\overline J_c\) denote the resulting regular restricted old matrix,
with row c zero. In the order (c, the other two states), write

\[
 \overline J_c=\begin{pmatrix}0&0\\h_c&T_c\end{pmatrix}.
 \tag{RQ14}
\]

The new matrix J_N=diag(X/L_N)A_N is restricted in the same way before
any specialization of its time factors. This defines regular extensions
of the matching entries, rather than evaluating uncancelled 0/0 formulas
at coincident lines.

Put r=q-1. Define 3-by-6 matrices D and V_k, 1<=k<=r, with rows c and
columns (a,b), a!=b, by

\[
 D_{c;a,b}=\begin{cases}
 G_{cb}\,e_bJ_N\overline J_c^{\,r}A_N^{-1}e_c,&a=c,\\
 0,&a\ne c,
 \end{cases}
 \tag{RQ15}
\]

and

\[
 (V_k)_{c;a,b}=\begin{cases}
 0,&a=c,\\[2pt]
 G_{ab}\dfrac{X_a}{L_a}
  \bigl[e_bJ_N\overline J_c^{\,k-1}e_c\bigr]
  \bigl[G(c,:)\overline J_c^{\,r-k}A_N^{-1}e_c\bigr],&a\ne c.
 \end{cases}
 \tag{RQ16}
\]

Entries with b=c also vanish, since row c of restricted J_N is zero.
These are the actual RQ4 residues: the shared-line case removes
X_a/L_ta directly; at another old block u, the residue of J_u divided
by X_c is e_c G(c,:). Counting old factors in the ascending word with
t omitted gives the block matrix of the full matching map:

\[
 M_{u,t}=\begin{cases}
 V_{u-1},&t<u,\\
 D,&t=u,\\
 V_u,&t>u.
 \end{cases}
 \tag{RQ17}
\]

In particular, same-state off-diagonal entries vanish: the source prefix
and the residue block contribute two X_c factors, while RQ4 removes only
one. At u=t the source has only its departure-state-a pole.

### Reduce the large matrix to small matrices

Write a left relation on M as z=(z_1,...,z_q), where each z_u is a
three-component row. Subtracting adjacent column-block equations gives

\[
 (z_{k+1}-z_k)P_k=0,\qquad P_k=D-V_k,\quad 1\le k\le r.
 \tag{RQ18}
\]

If every P_k has row rank 3, all z_u are equal. Any remaining
column-block equation is then

\[
 z_1 Z=0,\qquad Z=D+\sum_{k=1}^rV_k.
 \tag{RQ19}
\]

Thus rank(P_k)=rank(Z)=3 implies rank(M)=3q. This reduction uses the
actual coupled matrix; it does not add ranks of overlapping test groups.

The active matrices and columns from RQ14 are

\[
\begin{array}{c|c|c|c}
 c&\text{active states}&T_c&h_c\\ \hline
 0&(1,2)&
 \begin{pmatrix}35/29&21/29\\-22/51&-26/51\end{pmatrix}&
 \binom{7/29}{-2/51}\\[5pt]
 1&(0,2)&
 \begin{pmatrix}-3/4&-21/4\\1/10&13/10\end{pmatrix}&
 \binom{-3/2}{11/10}\\[5pt]
 2&(0,1)&
 \begin{pmatrix}11/9&22/9\\-1/6&-5/6\end{pmatrix}&
 \binom{77/9}{-1/2}
\end{array}
 \tag{RQ20}
\]

Each T_c has eigenvalues 1 and lambda_c, where

\[
 \lambda_0=-\frac{448}{1479},\qquad
 \lambda_1=-\frac9{20},\qquad
 \lambda_2=-\frac{11}{18}.
 \tag{RQ21}
\]

In particular, T_c is invertible and h_c is nonzero. The active
coordinate column X_active is a right eigenvector with eigenvalue 1.
Since L_c(Q_c)=0, the row G(c,active) annihilates that vector and is a
left eigenvector for lambda_c. Consequently,

\[
 G(c,\mathrm{active})T_c^l=\lambda_c^lG(c,\mathrm{active}),
 \qquad \overline J_c A^{-1}e_c=0.
 \tag{RQ22}
\]

### The endpoint matrices and the case q=2

First set A_N=A, still using the regular axis restrictions. Equation
RQ22 gives D=0 and V_k=0 for k<r. The surviving entries of V_r are

\[
 (V_r)_{c;a,b}=G_{ab}\frac{X_a}{L_a}
                (\overline J_c^{\,r})_{bc},
 \qquad \{a,b,c\}=\{0,1,2\}.
 \tag{RQ23}
\]

The three row supports are disjoint. Each row has a nonzero entry,
because its active column is T_c^(r-1)h_c, which is nonzero, and the
displayed scalar factors are nonzero. Hence V_r has rank 3. At this
specialization, P_r=-V_r and Z=V_r both have rank 3. When q=2, r=1,
these are all the matrices required by RQ18--RQ19.

### The remaining matrices P_k

For 1<=k<r, use the one-parameter specialization
A_N=A diag(1,1,d), and let d tend to positive infinity. In particular
r>=2. Take the 2-by-2 submatrix of P_k with rows 0,1 and columns
(0,2),(1,2). Put

\[
 D_0=D_{0;0,2},\quad D_1=D_{1;1,2},\quad
 W_0=(V_k)_{0;1,2},\quad W_1=(V_k)_{1;0,2}.
\]

Its determinant is D_0 D_1-W_0 W_1. For c=0,1, row 2 of J_N tends to
e_2. Equation RQ22 and
A_N^-1=diag(1,1,d^-1)A^-1 therefore give

\[
 D_c\longrightarrow-G_{c2}(T_c^r)_{22}(A^{-1})_{2c}.
 \tag{RQ24}
\]

Subscripts on T_c here use the original state labels. If a is the
other state in {0,1} and l=r-k>=1, the corresponding off-diagonal limit is

\[
 W_c\longrightarrow
 -(T_c)_{a2}(\overline J_c^{\,k-1})_{2c}
   \lambda_c^lG_{c2}(A^{-1})_{2c}.
 \tag{RQ25}
\]

The common scalar factors are nonzero. For k=1 both W limits vanish.
For k>=2, the limiting ratio W_c/D_c is

\[
 R_c=\frac{(T_c)_{a2}(\overline J_c^{\,k-1})_{2c}
                  \lambda_c^l}{(T_c^r)_{22}}.
 \tag{RQ26}
\]

The following exact bounds prove that the denominators are nonzero and
|R_0 R_1|<1. The two-eigenvalue identity

\[
 T_c^n=\frac{T_c-\lambda_c I}{1-\lambda_c}
       +\lambda_c^n\frac{I-T_c}{1-\lambda_c}
\]

and the active column T_c^(n-1)h_c of \(\overline J_c^n\) yield

\[
\begin{aligned}
 (T_0^r)_{22}&=-\frac{306}{1927}+\frac{2233}{1927}\lambda_0^r,\\
 (\overline J_0^n)_{20}&=-\frac{142}{1927}
                         +\frac{3388}{98277}\lambda_0^{n-1},\\
 (T_1^r)_{22}&=\frac{35}{29}-\frac6{29}\lambda_1^r,\\
 (\overline J_1^n)_{21}&=\frac{71}{58}
                         -\frac{18}{145}\lambda_1^{n-1}.
\end{aligned}
 \tag{RQ27}
\]

For r>=2, the first diagonal entry is negative and

\[
 |(T_0^r)_{22}|\ge
 \frac{306}{1927}-\frac{2233}{1927}\left(\frac{448}{1479}\right)^2
 =\frac{221184914}{4215198807}>\frac{13}{250}.
 \tag{RQ28}
\]

The last inequality follows from
250(221184914)=55296228500>54797584491=13(4215198807).
For n=1, the absolute value of the second entry in RQ27 is 2/51<17/200.
For n>=2, use 142/1927<37/500, 3388/98277<7/200, and
|lambda_0|<31/100 to get

\[
 |(\overline J_0^n)_{20}|<
 \frac{37}{500}+\frac{31}{100}\frac7{200}
 =\frac{1697}{20000}<\frac{17}{200}.
\]

Together with (T_0)_12=21/29<73/100 and l>=1, this gives

\[
 |R_0|<\frac{(73/100)(17/200)(31/100)}{13/250}
       =\frac{38471}{104000}<\frac{37}{100}.
 \tag{RQ29}
\]

Similarly, for r>=2,

\[
 (T_1^r)_{22}\ge\frac{35}{29}-\frac6{29}\left(\frac9{20}\right)^2
                 =\frac{6757}{5800}>\frac{29}{25}.
\]

For n=1, \((\overline J_1^n)_{21}=11/10\). For n>=2 it is positive
and at most 71/58+(18/145)(9/20)=32/25. Since |(T_1)_02|=21/4,

\[
 |R_1|<\frac{(21/4)(32/25)(9/20)}{29/25}
       =\frac{378}{145}<\frac{261}{100}.
 \tag{RQ30}
\]

Therefore |R_0 R_1|<9657/10000<1. The limiting 2-by-2 determinant is
nonzero. For k=1, the same diagonal bounds and the zero W limits give
the conclusion directly.

To obtain a three-row minor, add a column (2,b), b in {0,1}. Row 2 is
identically zero in the first two selected columns, because b=c=2 there.
On X_2=0, J_N=\(\overline J_2\)diag(1,1,d), and row 2 of every
positive power of \(\overline J_2\) is zero. Thus the added diagonal
entry is exactly

\[
 D_{2;2,b}=G_{2b}(d^{-1}-1)
              (\overline J_2^{\,q})_{b2}(A^{-1})_{22}.
 \tag{RQ31}
\]

At least one choice of b has a nonzero limit, since its active column
is T_2^(q-1)h_2, which is nonzero. The selected 3-by-3 determinant is
the preceding 2-by-2 determinant times D_(2;2,b). Other entries may
diverge as d tends to infinity, but they do not enter this determinant
expansion. Every P_k with k<r therefore has a nonzero rational minor.

### Genericity and the precise boundary of the result

For each fixed q, there are finitely many matrices P_k and Z. The
witnesses above show that a maximal minor of each is a nonzero rational
function of the same new time factors on the coalesced-old family.
The different minors need not be nonzero at the same displayed witness:
their product is nonzero in the parameter function field. Its
nonvanishing open contains positive choices of the new factors after
excluding the finitely many remaining denominator zeros. RQ18--RQ19 then
give a nonzero 3q minor of M.

The matching entries extend regularly to the old collision after the
axis restrictions and cancellations described above. The nonzero minor
therefore persists when the old time factors split to generic distinct
positive values. The additional geometric nonvanishing conditions can
also be imposed there. This proves the claimed generic rank 3q on the
incoming unequal-state subfamily RQ11 for every fixed q>=2 in the
common-G family.

The proof does not establish the rank of these matching functionals on
the joint kernel of the new-pole and coordinate-axis tests. In particular,
full rank 18q of the entire raw-boundary quotient remains unresolved;
the separate matching rank cannot be added to the preceding ranks.

This section was derived by the local raw-quotient reviewer from RQ4 and
the actual conjugated-product formulas. The primary researcher and the
independent deletion-induction reviewer checked the complete
argument; the finite modular checks are supporting evidence, not a
substitute for the uniform proof.

## Direct exact quotient certificates and a time-jet target

The script source24_raw_quotient.py evaluates the actual 18q boundary
columns directly under three groups of quotient observations. New-line
residues are stripped by the finite K_N inverse on each new line; axis
values use the conjugated products; matching values remove the departure
factor analytically. Ordinary evaluations away from forbidden poles suffice
for the lower-bound minors. No completeness of an undersampled restriction
is assumed.

| q | New poles | New poles + axes | All three groups | Full minor mod 1000003 |
|---:|---:|---:|---:|---:|
| 2 | 24 | 36 | 36 | 793485 |
| 3 | 33 | 54 | 54 | 792897 |
| 4 | 42 | 69 | 72 | 947021 |
| 5 | 51 | 84 | 90 | 484589 |
| 6 | 60 | 99 | 108 | 991289 |

The last column certifies full boundary rank at each recorded economic
fixture, including the newly checked q=5,6. Matching observations alone
have rank 3q on all boundary columns, on the incoming columns, and on
the incoming unequal-state subfamily in every case. These ranks are
computed separately from the nested ranks in the table; they are not
added. At q=4,5,6, matching contributes exactly 3q−9 additional directions
after the preceding groups.

The local run passed 53,460 actual-K versus conjugated-J new-residue
component comparisons. At q=2 it also passed 225 ordinary-kernel component
checks, 216 independently differentiated actual-K matching checks, and
4,329 zero observations on the entire appended old E/V/diagonal frame.
It took 0.7264 seconds with maximum RSS 21,233,664 bytes. The script
records exact points, row and column labels, hashes and minors. The
primary researcher read the complete implementation and checked its
source order, normalization and independent controls.

A subsequent local experiment targets a possible uniform proof. In
source24_raw_coalescent_jet.py, all old factors start at (1,1) and split as
(1+epsilon*t,1+epsilon*t²), t=1,...,q, with G from RQ12 and new factors
fixed at (2,3). Only ordinary points on the new lines and coordinate
axes are used; no coincident old-node residue matrix is evaluated.
For the resulting observation matrix M, let R be a basis of ker M(0).
The induced first derivative is measured by

\[
 \operatorname{rank}[M(0)\mid M'(0)R]
       -\operatorname{rank}M(0).
\]

This is the derivative on the actual leading kernel modulo the leading
image, not the rank of stacked jets. At q=2,3,4,5,6 the leading rank is 18.
The new-pole derivatives add 6,15,24,33,42 directions, respectively,
reaching 9q+6. With axes included, they add 18,36,51,66,81, reaching
min(18q,15q+9). Nonzero induced-derivative minors give finite generic
lower bounds after lifting from the recorded prime. They do not prove
the uniform first-jet statement or any upper bound from a deficient jet.
An extension also incorporates the regular coalesced matching matrix E0.
Let A denote the new-pole and axis matrix, F0=[A0;E0], and let R span
ker F0. The full quotient family has the rigorous lower bound

\[
 \operatorname{rank}F_0+
 \operatorname{rank}[A_0\mid A_1R]-\operatorname{rank}A_0.
\]

Indeed, every cokernel functional (L,0) with L A0=0 annihilates F0.
It observes the actual full derivative as L A1 R; no matching derivative
is required. The restriction to the joint kernel is essential. The
coalesced matching entries are evaluated only after the axis cancellations
in RQ4, so they have the required regular moving-point extension.
At q=2,3,4,5,6, rank F0 is 21,24,27,30,33 and the additional rank is
15,30,45,60,75. Thus this mixed first-jet construction certifies the full
18q boundary rank at all five fixtures. The extended run took 2.7402
seconds with maximum RSS 22,233,088 bytes. An independent reviewer
checked the complete code and both induced-derivative interpretations.

The next exact target is to prove this mixed first-time-jet rank
uniformly. The separate rank-3q matching theorem does not resolve
its derivative on the surviving joint kernel.

## The uniform joint leading kernel and its adjacent time jets

This section gives an exact paper reduction of the mixed-jet target.
It does not prove that the remaining derivative is injective for every
q. Keep the regular axis-restricted collision chart of RQ12--RQ17.
Write \(H=K(G)\), \(r=q-1\), and let \(A_0\) denote the leading
new-pole and coordinate-axis observation map. This may be the full
functional map, or fixed ordinary evaluations that separate its
18-dimensional leading image. Let \(E_0\) be the regular coalesced
matching map.

Choose as common columns the nine outgoing columns with first old block
1 and the nine incoming columns with shared old block 1. Replace each
remaining column by its adjacent difference: outgoing first \(k+1\)
minus first \(k\), and incoming shared \(k+1\) minus shared \(k\), for
\(1\le k\le r\). This is an invertible constant column change. At
coalescence \(A_0\) kills all these \(18r\) differences, because the
actual rational words within each group coincide.

The common 18 columns have rank 18 under new-pole observations alone,
by RQ6--RQ10 and their common positive witness. Therefore
\(\operatorname{rank}A_0=18\). This condition can be imposed
simultaneously with full row rank of every incoming \(P_k\) in RQ18:
their nonzero rational minors are functions of the same new time
factors with G fixed as in RQ12. The product of the rank-18 minor and
one nonzero minor for each \(P_k\) is nonzero in that parameter
function field. Positive choices outside the finitely many excluded
denominators consequently satisfy all the hypotheses together.

### Explicit matching matrices on the adjacent differences

Every formula in this paragraph is evaluated at the corresponding
matching point \(Q_c\) from RQ13, after restricting to \(X_c=0\).
Put \(J=\overline J_c\), \(g_c=G(c,:)\), and
\[
 f_{ab}=\frac{X_aA_N(a,b)}{L_{Na}}.
\]
If old block \(u\) occupies zero-based position \(p\) in the outgoing
move-first word, its matching entry is
\[
 f_{ab}\,(e_bJ^pe_c)\,
                  (g_cJ^{r-p}A_N^{-1}e_c). \tag{RQ32}
\]
This follows by replacing the residue block \(J_u\), divided by its
matching \(X_c\), by \(e_cg_c\) in the actual conjugated product.

In the adjacent difference with first block \(k+1\) minus first block
\(k\), every other old block has the same position. Block \(k\)
moves from position zero to \(k\), and block \(k+1\) moves from
position \(k\) to zero. Define the 3-by-9 outgoing matrix
\[
 (O_k)_{c;a,b}=f_{ab}
 \left\{\delta_{bc}\,g_cJ^rA_N^{-1}e_c
 -(e_bJ^ke_c)(g_cJ^{r-k}A_N^{-1}e_c)\right\}. \tag{RQ33}
\]
The matching difference is \(-O_k\) in old row block \(k\),
\(+O_k\) in row block \(k+1\), and zero elsewhere. In particular,
the entries with \(a=c\) vanish through \(X_a=0\); this factor has
not been removed.

For the incoming columns extend RQ15--RQ16 to all nine labels
\((a,b)\), including \(a=b\):
\[
 \begin{split}
 \widetilde D_{c;a,b}
 &=\mathbf1_{a=c}\,G_{cb}\,e_bJ_NJ^rA_N^{-1}e_c,\\
 (\widetilde V_k)_{c;a,b}
 &=\begin{cases}
 0,&a=c,\\
 G_{ab}\dfrac{X_a}{L_a}
       (e_bJ_NJ^{k-1}e_c)(g_cJ^{r-k}A_N^{-1}e_c),&a\ne c,
 \end{cases}\\
 \widetilde P_k&=\widetilde D-\widetilde V_k .
 \end{split} \tag{RQ34}
\]
The same residue calculation gives the incoming adjacent difference
as \(-\widetilde P_k\) in block \(k\) and
\(+\widetilde P_k\) in block \(k+1\). Its restriction to the six
unequal-state columns is the previously proved \(P_k\), so
\(\widetilde P_k\) has row rank 3 under the joint hypotheses.

Let
\[
 M_k=[\,O_k\ \ \widetilde P_k\,]:
             \mathbb R^{18}\longrightarrow\mathbb R^3 .
\]
The entire matching map on the adjacent differences is exactly
\[
 (z_1,\ldots,z_r)\longmapsto
   \sum_{k=1}^r
       (\mathbf e_{k+1}-\mathbf e_k)\otimes M_kz_k .
 \tag{RQ35}
\]
Here \(\mathbf e_k\) indexes old block positions, not outcomes.
The path-incidence map in (RQ35) is injective on
\((\mathbb R^3)^r\), and each \(M_k\) is onto. Consequently
\[
 \boxed{\quad
 \operatorname{rank}\begin{pmatrix}A_0\\E_0\end{pmatrix}
       =18+3(q-1)=3q+15,\qquad
 \ker\begin{pmatrix}A_0\\E_0\end{pmatrix}
       \simeq\bigoplus_{k=1}^{q-1}\ker M_k .
 \quad} \tag{RQ36}
\]
Each local kernel has dimension 15. Indeed, independence of the
common 18 columns first forces their coefficients to zero in a joint
kernel vector. The remaining equation is (RQ35), whose injective
path incidence forces \(M_kz_k=0\) separately for every edge.
This proves the leading count using the actual intersection of
kernels; it does not add ranks from separate observation tests.

### Exact derivatives of the prescribed words

Split the old factors by
\[
 A_t(\epsilon)=G\operatorname{diag}
       (1,\exp(\epsilon\tau_t),\exp(\epsilon\nu_t)),\qquad
 K_t(\epsilon)=H+\epsilon D_t+O(\epsilon^2).
\]
A common nonunit old time can first be absorbed into the columns of G.
With \(E_j\) the diagonal matrix having its sole nonzero entry at
\((j,j)\), put
\[
 U=HE_1-\operatorname{diag}(He_1)H,\qquad
 V=HE_2-\operatorname{diag}(He_2)H,\qquad
 D_t=\tau_tU+\nu_tV,\qquad
 \Delta_k=D_{k+1}-D_k. \tag{RQ37}
\]
Every \(D_t\) has zero row sum. If \(P_s\) is the actual move-s-first
old word and \(P^t\) is the increasing old word with \(t\) omitted,
then direct differentiation at zero gives
\[
 \begin{split}
 (P_{k+1}-P_k)'&=\Delta_kH^r-H^k\Delta_kH^{r-k},\\
 (P^{k+1}-P^k)'&=-H^{k-1}\Delta_kH^{r-k}.
 \end{split} \tag{RQ38}
\]
For example, the first formula telescopes the commutator sum
\(\sum_{i=0}^{k-1}H^i[\Delta_k,H]H^{r-1-i}\).
It uses the prescribed word order, not an arbitrary permutation.

The corresponding actual raw boundary derivatives are
\[
 \begin{split}
 (\widehat Q_{N,k+1,a,b}-\widehat Q_{N,k,a,b})'
 &=X_aK_N(a,b)e_b
          \{\Delta_kH^r-H^k\Delta_kH^{r-k}\},\\
 (\widehat Q_{k+1,N,a,b}-\widehat Q_{k,N,a,b})'
 &=X_a\Delta_k(a,b)e_bK_NH^r\\
 &\quad-X_aH(a,b)e_bK_NH^{k-1}\Delta_kH^{r-k}.
 \end{split} \tag{RQ39}
\]
Right multiplication by the fixed \(K_N^{-1}\) gives their stripped
versions. The incoming prefix derivative in the first term of the
second formula is essential. Its row sum is
\(X_a\Delta_k(a,b)\), whereas the insertion term is zero-sum.
The outgoing difference is zero-sum. Stripping preserves these row
sums, since \(K_N^{-1}\mathbf1=\mathbf1\).

These formulas also explain a cancellation of excessive old pole
orders. Near a coalesced old-line node, use a local coordinate \(L_c\)
and write
\[
 H=R_c/L_c+O(1),\qquad
 \Delta_k=-\ell_cR_c/L_c^2+O(L_c^{-1}),\qquad
 R_c=e_cv_c .
\]
Here \(v_c=G(c,:)\operatorname{diag}X\), and
\(\ell_c=(\tau_{k+1}-\tau_k)G(c,1)X_1+
(\nu_{k+1}-\nu_k)G(c,2)X_2\), evaluated at the pole.
The two potential order-\((q+1)\) terms in the first line of
(RQ38) are identical and cancel. In an incoming difference with
shared state \(a=c\), the derivative of its prefix and the insertion
term likewise have opposite order-\((q+1)\) coefficients. For
\(a\ne c\), the prefix row is regular at this pole and that order
does not occur. Thus all adjacent boundary first jets have old pole
order at most \(q\). The same calculation applies after taking a
new-line residue; its fixed new-kernel factors do not alter the
cancellation. This is a pole-order bound, not a claim of independence
of all resulting coefficients.

### The remaining uniform mixed-jet question

Apply the new-pole and axis observations to (RQ39), and denote the
result on edge k by \(A_{1,k}(\Delta_k)\). The exact open target is
injectivity of
\[
 \bigoplus_{k=1}^{q-1}\ker M_k
    \longrightarrow \operatorname{coker}A_0,\qquad
 (z_k)_k\longmapsto
       \left[\sum_kA_{1,k}(\Delta_k)z_k\right] .
 \tag{RQ40}
\]
Its domain has dimension \(15(q-1)\). The time increments in
\(\Delta_k\) may be chosen independently through the consecutive
differences of \(\tau_t,\nu_t\). If (RQ40) is injective for one
admissible common-G choice for each q, the genuine mixed-jet argument
above yields rank
\(3q+15+15(q-1)=18q\), without needing a matching derivative.
The recorded q=2,...,6 checks verify this at their finite fixtures.
The all-q injectivity in (RQ40) is not established here.

The primary researcher and the independent deletion-induction reviewer
checked the matching formulas, common-parameter argument, incidence
decomposition, actual word derivatives and pole-order cancellation in
this section. These are audited paper results; no Lean formalization
of the new joint-kernel reduction is claimed.

## Old-pole coefficients and an endpoint-distance filtration

**Status of this section: independently audited paper results; not Lean
formalized.** The primary researcher and the independent
deletion-induction reviewer checked the coefficient identities and
spectral pole bounds, including the moving-pole hypothesis.
It refines the pole-order calculation after (RQ39), but does not prove
the injectivity in (RQ40). All coefficient spaces for source relations
still use constant real scalars.

Fix one generic point of an old line, take its local equation as
\(z=L_c\), and assume the other old lines do not vanish there. Write
\[
 H=\frac Rz+S+O(z),\qquad
 R=e_cv_c,\qquad R^2=sR,\qquad
 s=\operatorname{tr}R=G_{cc}X_c\ne0. \tag{RQ41}
\]
This hypothesis holds at the generic old poles on a new-line restriction,
and at generic coordinate-axis poles whose departure state differs from
the axis state. It fails at the matching point \(L_c=X_c=0\), where
the residue is nilpotent. The spectral argument below is not a statement
at that matching point; the matching equations remain the separate
constraints \(M_kz_k=0\).

Let \(D\) be a fixed actual common-time derivative, that is, a fixed
linear combination of \(U,V\) in (RQ37). Its local expansion and a
useful commutator coefficient are
\[
 D=-\frac{\ell R}{z^2}+\frac Tz+O(1),\qquad
 W=T+\ell S,\qquad C=[W,R],\qquad
 [D,H]=\frac C{z^2}+O(z^{-1}),\qquad RCR=0. \tag{RQ42}
\]
Here \(\ell\) is the value at the pole of the derivative of its line
equation. The notation \(T\) in this local expansion does not denote
the observation map \(T_N\). Indeed, the potential order-three term
in \([D,H]\) cancels, and its order-two term is
\([T,R]-\ell[R,S]=[T+\ell S,R]\).

Put \(r=q-1\), and for the moment use the same \(D\) on every edge.
The outgoing word derivative is
\[
 \mathcal O_k(D)=DH^r-H^kDH^{r-k}
   =\sum_{i=0}^{k-1}H^i[D,H]H^{q-2-i}.
 \tag{RQ43}
\]
For \(q\ge3\), its coefficient of \(z^{-q}\) is
\[
 [z^{-q}]\mathcal O_k(D)=
 \begin{cases}
 CR^{q-2},&1\le k\le q-2,\\
 CR^{q-2}+R^{q-2}C,&k=q-1.
 \end{cases} \tag{RQ44}
\]
Every term having a positive power of R on both sides of C is zero.
For \(q=2\) there is one edge and its coefficient is C. Thus the
highest outgoing pole does not distinguish the interior edges for a
fixed time direction. The actual outgoing derivative includes the
left factor \(X_aK_N(a,b)e_b\) from (RQ39). After taking a new-line
residue in sector a this factor becomes
\(X_aA_N(a,b)X_be_b\), followed by the fixed right strip
\(K_N^{-1}\). These factors must be retained when applying observations;
they can annihilate the displayed coefficient.

For incoming derivatives retain the differentiated prefix. With
\(w=e_bK_N\), or \(w=v_{Nb}\) after its new-line residue, define
\[
 \mathcal I_k(D)=X_aD(a,b)wH^r
       -X_aH(a,b)wH^{k-1}DH^{r-k}.
 \tag{RQ45}
\]
At the first edge its order-q coefficient is
\[
 [z^{-q}]\mathcal I_1(D)
 =X_a\{W_{ab}wR-R_{ab}wW\}R^{q-2},
\]
and consecutive coefficients differ by
\[
 [z^{-q}](\mathcal I_{k+1}(D)-\mathcal I_k(D))
 =X_aR_{ab}wR^{k-1}CR^{q-k-2},
 \qquad 1\le k\le q-2. \tag{RQ46}
\]
All quantities in these leading coefficients are evaluated at the pole.
For \(q\ge4\), the order-q incoming coefficients consequently agree
on all bulk edges \(2\le k\le q-2\); only the first and last edge
can give a change. If \(a\ne c\), then \(R_{ab}=0\), so this top
coefficient agrees on all edges. Formula (RQ46) follows from the exact
identity
\(\mathcal I_{k+1}-\mathcal I_k
=X_aH(a,b)wH^{k-1}[D,H]H^{q-k-2}\).

### The moving pole and the analytic complementary block

The regularity needed for sharper bounds uses the actual moving pole.
Replace the exponential time curve by its affine curve with the same
first derivative. Its line equation has the exact form
\(\zeta(z,t)=z+t\ell(z)\). The matrix \(\zeta H(z,t)\) is jointly
analytic. In general \(zH(z,t)\), with z fixed at the old line,
is not jointly analytic. At \(\zeta=0\) the former matrix has rank
one and a simple nonzero eigenvalue. Its analytic eigenvalue and spectral
projector, denoted by \(\gamma\) and P, give
\[
 H(z,t)=\lambda(z,t)P(z,t)+B(z,t),\qquad
 \lambda=\gamma/\zeta,\qquad PB=BP=0,
 \tag{RQ47}
\]
where P and B are jointly analytic. To see the last assertion,
\(\zeta H-\gamma P\) vanishes on \(\zeta=0\), so each of its
entries is divisible by \(\zeta\). At \(t=0\),
\(\lambda=s/z+O(1)\) and \(P(0)=R/s\).

With \(Q=I-P\), differentiating the actual family gives
\(QDQ=QB_tQ\), which is analytic: the \(\lambda_tP\) term is
killed and \(QP_tQ=0\). Consequently the P--P block of \([D,H]\)
is zero, its two off-diagonal P--Q blocks have pole order at most two,
and its Q--Q block is analytic. Therefore, for all \(i,j\ge0\),
\[
 \operatorname{poleord}\bigl(H^i[D,H]H^j\bigr)
       \le \max(i,j)+2. \tag{RQ48}
\]
Here a pole-order bound p means the expression is \(O(z^{-p})\);
it need not have a nonzero coefficient at that order. This argument
requires an actual parameter derivative D. It does not assert the
regularity of \(QDQ\) for an arbitrary matrix with double poles.

For an explicit coefficient map put
\(P_0=R/s\), \(Q_0=I-P_0\), and \(B_0=Q_0SQ_0\). In the
following projector formulas interpret \(B_0^0\) as \(Q_0\).
The coefficient at the bound in (RQ48) is
\[
 \begin{cases}
 s^iP_0CB_0^j,&i>j,\\
 s^jB_0^iCP_0,&j>i,\\
 s^i(P_0CB_0^i+B_0^iCP_0),&i=j.
 \end{cases} \tag{RQ49}
\]
This follows by splitting the product into its two off-diagonal
projector blocks and its analytic complementary block. The given source
prefixes and output observations still act on these coefficient maps.

Using the exact consecutive-edge identities in (RQ43) and (RQ46),
one obtains, for \(q\ge3\) and \(1\le k\le q-2\),
\[
 \begin{split}
 \operatorname{poleord}(\mathcal O_{k+1}(D)-\mathcal O_k(D))
   &\le q-\min(k,q-k-2),\\
 \operatorname{poleord}(\mathcal I_{k+1}(D)-\mathcal I_k(D))
   &\le q-\min(k-1,q-k-2).
 \end{split} \tag{RQ50}
\]
The second bound improves by one when the prefix row \(a\ne c\).
Thus deeper interior differences lose successive highest pole levels.
An analytic left or right factor preserves these upper bounds, although
it can kill the first allowed coefficient.

### Coordinate-axis observations and the remaining restriction

The axis observations should be applied after their coordinate factors
have been cancelled, rather than by substituting into a singular
\(\operatorname{diag}(X)^{-1}\). Use
\(J=\operatorname{diag}(X)H\operatorname{diag}(X)^{-1}
=\operatorname{diag}(X/L)G\), and similarly \(J_N\). The actual
raw columns divided on the right by \(\operatorname{diag}(X)\)
and then multiplied by \(A_N^{-1}\), as in (RQ2), are
\[
 \begin{split}
 C^{\rm out}_{s,ab}
   &=\frac{X_aA_N(a,b)}{L_{Na}}\,
       e_b J_sJ_{\text{remaining in increasing order}}A_N^{-1},\\
 C^{\rm in}_{t,ab}
   &=J_t(a,b)e_bJ_N
       J_{\text{increasing old word omitting }t}A_N^{-1}.
 \end{split} \tag{RQ51}
\]
These formulas have regular restrictions to an axis away from their
listed line poles. At an old pole of state c different from that axis,
J has residue \(X_ce_cG(c,:)\) with the same nonzero trace s.
Consequently (RQ42)--(RQ50) apply to \(J,\dot J\), with the analytic
outgoing prefactor in (RQ51). For the incoming formula replace
\(X_aH(a,b)\) by \(J(a,b)\), its derivative accordingly, and
take \(w=e_bJ_N\). This keeps the prefix term and avoids hidden
coordinate divisions. Taking the selected output component and any
regular new-line factor can only decrease the resulting pole bound.

The endpoint-distance filtration is for fixed D. In the actual mixed-jet
problem the direction is \(\Delta_k\) and may vary with k; moreover
the coefficient vector on edge k must lie in its own \(\ker M_k\).
Replacing adjacent-edge columns by their differences need not preserve
this direct sum of local constraints. Hence (RQ44), (RQ46), and (RQ50)
provide explicit coefficient maps and a possible lower-pole filtration,
but not a triangular basis on the domain of (RQ40). Uniform injectivity
of that constrained map remains open.

### Finite coefficient profiles and a common time direction

`source24_edge_filtration.py` applies the actual RQ39 derivatives to
the 15-dimensional kernels in RQ36 at q=3,4. It records exact Laurent
coefficients on the new lines and coordinate axes. Every profile uses
the same 18 common leading columns B and computes
rank[B|D]−rank B; combining channels therefore requires one shared
leading correction. The time increments remain the actual (1,2k+1).

| q | Cumulative gains, old pole orders q down to 1 | With fixed new-axis poles | Complete gain |
|---:|---|---:|---:|
| 3 | 6, 12, 27 | 30 | 30 |
| 4 | 6, 12, 27, 42 | 45 | 45 |

At each of the two highest layers, the new-line channel and the axis
channel separately have zero induced gain. Their combined gains are
nevertheless 6 and 12. This is an explicit example of the necessary
cross-channel compatibility of the leading correction, rather than a
sum of separate ranks. At both fixtures the old-pole coefficients leave
three directions; fixed new-axis poles supply them. The polynomial
remainders add no further directions there. No triangular separation
of the local edge kernels is inferred.

The code verifies the path-incidence signs and coverage of the joint
leading kernel. It checks 6,048 components against separately multiplied
actual dual words, 2,997 rational reconstruction components and 4,536
excess-order coefficients. Laurent tails retain their precision; the
minimum certified cutoff is 5. New-line polynomial remainders have
degree at most two and axis remainders are constant, so the saved
principal coefficients and remainders describe the entire restrictions.
The run took 1.3405 seconds with maximum RSS 21,413,888 bytes. The
primary researcher and independent deletion-induction reviewer checked
the implementation and saved `source24-edge-filtration-results.json`.

A separate bounded run asks whether varying the direction with k is
necessary at these two fixtures. In `source24_raw_coalescent_jet.py`,
the optional direction map sets old factors to
(1+epsilon*t,1+3*epsilon*t), so every increment is U+3V. The mixed
leading rank and derivative gain are again 24+30=54 at q=3 and
27+45=72 at q=4. Its exact inputs and certificates are saved separately
in `source24-raw-common-direction-results.json`; the default quadratic
direction and its record are unchanged. The primary researcher checked
the small parameterization and the saved result. This run took 0.6238
seconds with maximum RSS 17,580,032 bytes.

These are finite lower-bound certificates and fixture profiles. In
particular, common increments suffice at these two witnesses, but
neither arbitrary common directions nor all-q injectivity is proved.

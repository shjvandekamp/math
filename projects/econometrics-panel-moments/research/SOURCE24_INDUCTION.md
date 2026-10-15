# Equation (24): an induction and a quadratic-size residue test

Research note, 15 October 2026. The algebraic arguments below reduce the
three-choice independence problem to explicit finite determinants and prove
generic nonvanishing of the shared-new polar half. Some supporting source
recursion statements, the actual source-to-ordered-product identities, and
the binary moved-word rank theorem are now formalized in Lean;
[STATUS.md](../STATUS.md) gives the exact scope. The
polar theorem is a paper proof. Nonvanishing of the remaining regular Schur
half for every panel length remains unproved, so the complete all-length
source-independence claim remains open.

## Exact split of the source family

Use the paper's one-based time labels and three alternatives. Its restriction
on the shared positions is

\[
 t_r=r\qquad(1\le r\le \max(0,j-1)).
\]

Consequently, the equation (24) columns whose shared set contains period 1
are exactly three indicator lifts of the complete source family for the
remaining \(T-1\) periods: fix \(y_1=a\), delete the first shared position,
shift the other time labels, and use initial outcome \(a\). Their supports
for different \(a\) are disjoint. The remaining columns have either
\(j=0\), or \(j=1\) with shared position \(t\ge2\). Put \(n=T-2\). Their
number is

\[
 3n+9n(n-1)=3n(3n-2)
 =\ell(3,T)-3\ell(3,T-1).
\]

Thus, once the shorter source family is a basis, independence at length
\(T\) reduces to independence of these new columns modulo the three
conditional moment spaces for the shorter panel.

## An explicit quotient map

Let \(X=(X_0,X_1,X_2)\) be homogeneous effect coordinates. Index the
transition following outcome \(y_t\) by \(t\). Thus its coefficient matrix
is the paper's time-\(t+1\) index table. For \(t\in B:=\{2,\ldots,T-1\}\),
write

\[
 L_{ta}=\sum_i A_t(a,i)X_i,\qquad
 v_{ta}=(A_t(a,i)X_i)_i,\qquad
 K_t=\operatorname{diag}(L_{t0},L_{t1},L_{t2})^{-1}A_t
       \operatorname{diag}(X_0,X_1,X_2).
\]

All vectors below are row vectors. Each \(K_t\) has row sum one. Let
\(P_s^C\) denote the product of the matrices indexed by a nonempty set
\(C\), with \(s\in C\) first and all remaining indices in increasing
order. An empty product is the identity.

For a moment \(m\), the three rational functions

\[
 C_i(X)=\sum_{y:y_1=i}m(y)p_y(X)
\]

are its image modulo the three shorter conditional moment spaces: their
joint kernel is precisely the direct sum of those spaces. For source
columns, compute these functions by replacing the likelihood times its
scale ratio by the transformed-chain likelihood, then summing the chain
after the occurrence of \(y_1\). These sums telescope because the matrices
have row sum one.

Multiply all three components by the common initial denominator and divide
each column by its nonzero initial-row coefficient. The new source columns
then have the following images:

\[
 F_{s,a}=X_a e_a(I-P_s^B),\qquad s\in B,
\]

and

\[
 F_{t,s,a,b}=X_aK_t(a,b)e_b(I-P_s^{B\setminus\{t\}}),
 \qquad t,s\in B,\quad t\ne s.
\]

Here \(a\) is the value of the shared outcome \(y_t\), and \(b\) is the
value at the position where the two orders first differ. These formulas
retain the paper's precise increasing-order suffix convention.

The quotient images depend only on the tail matrices with indices in
\(B\). The transition following period 1 disappears in the telescoping
sum. The initial outcome changes only the nonzero column factors removed
above. More generally, every source numerator has the initial-row
coefficient of its fixed first-generated state as a column factor, while
the original likelihood numerator supplies nonzero row factors. Thus
source rank is the same for every initial outcome at a positive table.

## The zeroth-level columns reduce exactly to single-block relations

Define

\[
 E_{t,a}=X_a e_a(I-K_t).
\]

For \(n\ge2\), choose \(r=\min(B\setminus\{s\})\). The elementary
identity \(I-K_sP=(I-K_s)+K_s(I-P)\) gives

\[
 F_{s,a}=E_{s,a}+\sum_b F_{s,r,a,b}.
\]

Therefore subtracting the displayed sum of first-level columns replaces
each zeroth-level column by \(E_{s,a}\). This is an invertible column
operation with constant coefficients. No coefficient depending on \(X\)
is used. When \(n=1\), the equality \(F_{s,a}=E_{s,a}\) is immediate.

## A canonical basis of the quotient relation space

Let

\[
 D=\prod_{t\in B}\prod_a L_{ta},
\]

and let \(Z\) be the union of the six base points of each block, as in
the structural dimension proof. Consider the real vector space

\[
 W_n=\left\{\left(\frac{X_i g_i}{D}\right)_i:
 g_i\in I(Z)_{3n},\quad \sum_i X_i g_i=0\right\}.
\]

Under the primitive conditions of the structural theorem, this is the
quotient of the full moment space by the three shorter conditional moment
spaces. Indeed, splitting the cleared polynomial by \(y_1=i\) gives a
relation \(\sum_i h_i c_i=0\) for the first cubic block. The one-block
divisibility argument gives \(c_i=L_i g_i\) and \(\sum_iX_i g_i=0\).
Cross-block nonincidence makes \(c_i\) vanish at every tail base point if
and only if \(g_i\) does. The tail span theorem identifies the admissible
\(c_i\) with the required tail product space.

For completeness, its dimension is

\[
 \dim W_n=3\dim I(Z)_{3n}-\dim I(Z)_{3n+1}
 =3n(3n-2).
\]

The coordinate map \(I(Z)_{3n}^3\to I(Z)_{3n+1}\) is onto. Start with
any homogeneous coordinate decomposition of a polynomial in the target.
At each base point its three coefficients form a coordinate syzygy.
Interpolate the three scalar Koszul correction values in degree \(3n-1\)
using the already constructed global separators. Subtract those
corrections to make each coefficient vanish at every base point without
changing its coordinate combination. Surjectivity and the established
evaluation dimensions give the displayed count.

In addition to the \(E_{t,a}\), define the **local pair** vectors

\[
 B_{t,s,a,b}=X_aK_t(a,b)e_b(I-K_s),\qquad t\ne s.
\]

Retain the primitive structural conditions used above, and impose the
following additional, explicit geometry conditions:

1. All transition coefficients used as scalars are nonzero.
2. Every intersection of a line from one block with a line from another
   block has all three coordinates nonzero.
3. No third denominator line passes through such an intersection.

These conditions are stronger than those needed for the dimension theorem.
They are finite polynomial nonvanishing conditions after choosing
cross-product representatives. Distinct positive conic parameters
\(L(w)=X_0+wX_1+w^2X_2\) satisfy them: their pair intersection is
\((uv,-u-v,1)\), and a third line evaluates to \((w-u)(w-v)\).

**Lemma.** Under these conditions, the \(3n\) single-block vectors \(E\)
and the \(9n(n-1)\) ordered local-pair vectors \(B\) form a basis of
\(W_n\).

**Proof.** First they belong to \(W_n\). Their row sums are zero.
Multiplication of component \(i\) by \(D/X_i\) gives a polynomial. For
\(E_{t,a}\), its component \(a\) is

\[
 \frac{D}{L_{ta}}\sum_{c\ne a}A_t(a,c)X_c,
\]

and its other components are \(-A_t(a,i)X_aD/L_{ta}\). For
\(B_{t,s,a,b}\), its component \(b\) is

\[
 A_t(a,b)X_a\frac{D}{L_{ta}L_{sb}}
       \sum_{c\ne b}A_s(b,c)X_c,
\]

and its other components are
\(-A_t(a,b)A_s(b,i)X_aX_bD/(L_{ta}L_{sb})\).
These expressions vanish at every within-block pair intersection. At a
coordinate base point \(L_{ta}=X_a=0\) or \(L_{sb}=X_b=0\), the displayed
sum in the exceptional component also vanishes. The remaining blocks
contribute unchanged denominator factors. Thus all coefficient polynomials
belong to \(I(Z)_{3n}\).

Consider any constant linear relation among these vectors. At the
cross-block point \(P=\{L_{ta}=L_{sb}=0\}\), multiply that relation by
\(L_{ta}L_{sb}\) and evaluate. Only two local-pair columns survive, namely
\(B_{t,s,a,b}\) and \(B_{s,t,b,a}\). Their values are

\[
 -A_t(a,b)X_a(P)X_b(P)v_{sb}(P),\qquad
 -A_s(b,a)X_a(P)X_b(P)v_{ta}(P).
\]

They are independent. Both \(v\)-vectors have row sum zero, and multiplying
the two independent line-coefficient vectors by the invertible diagonal
matrix \(\operatorname{diag}(X(P))\) preserves their independence.
Therefore the two corresponding coefficients in the linear relation are
zero. Applying this argument at each cross-block line pair kills every
\(B\) coefficient. A single-line residue then kills each remaining
\(E_{t,a}\) coefficient: its residue is the nonzero polynomial vector
\(-X_a v_{ta}\) on that line. All columns are independent, and their count
equals \(\dim W_n\). ∎

This lemma does **not** replace the specified source family by a theorem
about that family. Its value is to provide explicit coordinates for the
remaining source-independence question.

## The exact remaining determinant

For each unordered cross-block line pair
\(\{(u,c),(v,d)\}\), evaluate

\[
 \rho_{uc,vd}(F)
   =\left.(L_{uc}L_{vd}F)\right|_{P_{uc,vd}}.
\]

This lies in the two-dimensional zero-sum row space. Express it in the
ordered basis \((v_{uc}(P),v_{vd}(P))\). An implementation can choose any
nonzero two-by-two coordinate minor of those two vectors; independence
ensures at least one exists. Equivalently, use the scaled pair-residue
vectors appearing in the lemma to obtain the actual \(B\) coefficients.

Collect these two coordinates for every unordered cross-block line pair.
There are \(9\binom n2\) such pairs. On the \(9n(n-1)\) first-level source
columns \(F_{t,s,a,b}\), this produces a square matrix

\[
 R_n(A)\in\mathbb R^{9n(n-1)\times9n(n-1)}.
\]

All single-block vectors \(E\) have zero double-pole residues. The canonical
basis lemma therefore shows

\[
 \text{new source columns are independent in the quotient}
 \quad\Longleftrightarrow\quad \det R_n(A)\ne0.
\]

Together with the lifted-family induction this is an exact sufficient
route to independence of equation (24) for all \(T\). For \(T=5\), the
matrix has size 54; for \(T=6\), size 108. Its entries can be evaluated
using only three-by-three transfer-matrix products and cross-product
points. No enumeration of the \(3^T\) paths or expansion of homogeneous
polynomials is necessary.

The sufficiency direction actually requires less than the full quotient
identification. Suppose only that the shorter source family is independent
and \(R_n\) is invertible. Apply the conditional-sum map to a relation
among length-\(T\) source columns; it kills all lifted columns. Perform
the exact zeroth-level column reduction. Double-pole residues and
invertibility of \(R_n\) kill the remaining first-level coefficients.
Single-line residues then kill the \(E\) coefficients. What remains is a
relation among the three disjoint shorter-family lifts, whose independence
kills every coefficient. This argument does not assume shorter-family
completeness or that \(W_n\) exhausts the quotient.

To compute an entry, multiply the relevant rational expression for
\(F_{t,s,a,b}\) by the two pole factors before substituting the point.
For a pole belonging to a matrix \(K_u\), replace that factor in the
matrix word by its residue matrix, which has only the appropriate row
nonzero, equal to \(v_{uc}(P)\). All other matrix factors evaluate
ordinarily at \(P\). If the pole belongs to the scalar prefactor
\(K_t(a,b)\), its residue is \(A_t(a,b)X_b(P)\). A column missing one of
the two pole factors contributes zero. These instructions avoid evaluating
an undefined \(0/0\) expression.

For the economic family, the entries are rational functions of exponential
index coefficients on the stated geometry region. Clearing the explicitly
nonzero denominators gives an analytic exceptional factor. A nonzero
economic witness for each \(n\), together with the inherited shorter
factor, would yield the desired nonempty open dense region by the same
analytic argument as the existing finite theorem.

## What remains open

The new mathematical gap is an all-\(n\) nonvanishing theorem for
\(R_n\) on the economic parameter family. The single-block reduction is
exact, but naively stripping the suffix from a first-level source column
introduces a second shared position. Such a column is outside the new
part of the restricted equation (24) family. Multiplying columns by
functions of \(X\) is not a valid independence-preserving column operation.

One can reduce the resulting rational vectors to the canonical \(E,B\)
basis by partial fractions in three variables, but this alone does not
prove the resulting square change-of-basis matrix invertible. Primitive
geometry, the dimension formula, and a count of the source columns are
therefore insufficient substitutes for this missing nonvanishing proof.

One exact transformation may help organize an induction. Suppose all
coefficient matrices are invertible and let \(N=\max B\). Right
multiplication of every rational row vector by \(K_N^{-1}\) is an
injective real-linear operation, despite its dependence on \(X\). For
\(t,s<N\), the new block is last in the increasing suffix, so

\[
 F^{B}_{t,s,a,b}K_N^{-1}
 =F^{B\setminus\{N\}}_{t,s,a,b}
  +X_aK_t(a,b)e_b(K_N^{-1}-I),
\]

with the analogous identity for zeroth-level columns. The formula

\[
 K_N^{-1}=\operatorname{diag}(X)^{-1}A_N^{-1}
           \operatorname{diag}(L_N)
\]

shows that these transformed old-index columns have no denominator from
the new block. Columns with \(t=N\) or \(s=N\) can still have such poles.
This suggests a filtration by new-line residues. It does not finish an
induction: on a new line \(L_{Na}=0\), the restriction of \(K_N^{-1}\) to
zero-sum row vectors generically has rank one. New-line residues therefore
retain only one of the two cross-pair coordinates; a second argument must
control the information transferred to old-line residues or regular
parts. This approach has not yet produced an all-\(n\) determinant proof.

There is also an exact block structure directly in \(R_n\). For a
cross-point involving two old blocks, and a source column with both
indices old, the double residue is its old double residue multiplied on
the right by \(K_N(P)\). The correction
\(X_aK_t(a,b)e_b(I-K_N)\) has at most one old pole and contributes zero.
Thus the old-row, old-column block is \(R_{n-1}\) followed by independent
invertible two-dimensional coordinate changes at the old cross-points,
whenever those \(K_N(P)\) are invertible. This gives a Schur-complement
reduction with \(18(n-1)\) new rows and columns. It does not prove that the
Schur complement is nonsingular.

The remaining determinant can be isolated more precisely. Put
\(m=n-1\). At each old-new cross-point, expand the residue vector
in the basis \((v_{\mathrm{old}},v_N)\), and call its two scalar
coordinates \(\alpha,\beta\), respectively. Order the rows as
old-old residues, old-new \(\alpha\), old-new \(\beta\), and
the columns as old-old source pairs, pairs with \(t=N\), and pairs
with \(s=N\). The exact block matrix is

\[
 R_n\sim
 \begin{pmatrix}
 O&D&E\\
 0&P&Q\\
 B&R&S
 \end{pmatrix}. \tag{S1}
\]

Here \(O\) is the transported old residue matrix just described,
and each of the last two row or column groups has size \(9m\).
The zero block is exact: in every old-old source column, \(K_N\)
is last in the word, and its new-line residue is parallel to \(v_N\).
The polar theorem below proves that \(P\) is generically invertible
on the common-\(G\), independent-time family. Assuming also that
\(O\) is invertible, ordinary constant-matrix elimination leaves
the single \(9m\)-square target

\[
 H=S-BO^{-1}E-(R-BO^{-1}D)P^{-1}Q. \tag{S2}
\]

In the displayed row and column orders,
\(\det R_n=\det O\det P\det H\), with the coordinate-change
and permutation factors restored when comparing to the original
matrix. Proving generic nonvanishing of \(H\) for every \(m\)
is the remaining regular-half problem; the polar theorem alone does
not prove it.

The independent finite calculation `exploration/source24_schur.py`,
recorded in `exploration/source24-schur-results.json`, verifies (S1),
(S2), the transported old block, and the determinant factors with
permutation signs at six asymmetric positive fixtures. They use
\(G=\left(\begin{smallmatrix}1&1&1\\1&30&10\\1&3&2\end{smallmatrix}\right)\),
\(m=2,3,4\), economic old time factors, and new factors
\((1,\varepsilon,\varepsilon^3)\) at
\(\varepsilon=1/7,2/11\). In these exact modular checks the
regular matrices have full ranks \(18,27,36\), respectively.
These are finite witnesses, not an all-length proof for (S2).

The two halves of the inverse-matrix filtration can be described exactly.
Write \(n=m+1\), let \(D_{\mathrm{old}}\) be the product of the old lines,
and retain invertibility of \(A_N\). The vectors in \(W_nK_N^{-1}\) with
no pole on any new line are precisely

\[
 \frac{f}{D_{\mathrm{old}}},\qquad
 f_i\in I(Z_{\mathrm{old}})_{3m+1},\quad
 \sum_i f_i=0,\quad f_a(R_{Na})=0\quad(a=0,1,2).
\]

To verify this, multiply back by \(K_N\). The resulting coefficient
polynomials in the definition of \(W_n\) are

\[
 g_i=\sum_j f_j A_N(j,i)\frac{D_N}{L_{Nj}},
 \qquad D_N=\prod_j L_{Nj}.
\]

At an old base point, the diagonal factors \(D_N/L_{Nj}\) and the matrix
\(A_N\) are invertible, so all \(g_i\) vanish exactly when all \(f_i\)
vanish. At a new within-block pair point, every \(D_N/L_{Nj}\) is zero.
At \(R_{Na}\), only the term \(j=a\) can survive, giving exactly
\(f_a(R_{Na})=0\). Row-sum zero is preserved by both matrices.

The canonical local-pair columns \(B_{N,t,a,b}K_N^{-1}\) give
\(9m\) independent new-line pole coordinates. At their own cross-point,
the old-line residue direction is independent of \(v_{Na}\), the row
kernel of \(K_N^{-1}\) there, so the transformed residue is nonzero.
All other such pair coordinates are zero. The transformed old canonical
basis, the three \(E_{N,a}K_N^{-1}\), and the \(9m\) columns
\(B_{t,N,a,b}K_N^{-1}\) have no new-line pole. Consequently the pole
image has dimension \(9m\), and its kernel has dimension
\(\dim W_m+9m+3\). This explains the two groups of new coordinates
without identifying them as independent coordinates for the specified
long-suffix source columns. That last inference remains open.

The regular part also has explicit coordinates at the intersections with
coordinate axes. These are paper linear-algebra lemmas, not a proof of
nonvanishing of (S2). Define the homogeneous linear zero-sum rows

\[
 H_b(X)=e_bA_N^{-1}\operatorname{diag}(L_N)-X_be_b,
 \qquad
 C_{t,a,b}=B_{t,N,a,b}K_N^{-1}
       =A_t(a,b)\frac{X_a}{L_{ta}}H_b(X). \tag{S3}
\]

Let \(\mathcal N\) be the no-new-pole space described above. In
addition to the earlier structural assumptions, require that every
coordinate-edge intersection
\(P_{t,a;i}=\{L_{ta}=X_i=0\}\), for all \(i\), lies on no
other old or new denominator line. This follows from the cross-block
coordinate nonvanishing assumption for lines in different blocks and
must also hold for the remaining within-block incidences. Retain all
nonzero coefficients used below; in particular the off-diagonal entries
of \(A_N\) are nonzero. Then

\[
 \mathcal N=W_m\oplus\operatorname{span}\{C_{t,a,b}\}
                    \oplus\operatorname{span}\{H_0,H_1,H_2\}.
 \tag{S4}
\]

Here \(W_m\) is the untransformed old space. It belongs to
\(\mathcal N\): its component \(i\) has a factor \(X_i\),
so the extra condition at \(R_{Ni}\) holds. The \(H_b\) belong
to \(\mathcal N\) because \(H_b=E_{N,b}K_N^{-1}\).
For a direct coordinate proof of (S4), write
\(\mathcal R_{ta}(g)=(L_{ta}g)|_{L_{ta}=0}\). For \(i\ne a\)
define

\[
 \Gamma_{t,a;i}(g)=
  \frac{\mathcal R_{ta}(g)_i(P_{t,a;i})}
       {X_a(P_{t,a;i})L_{Ni}(P_{t,a;i})},
\]

and for \(i=a\) first divide \(\mathcal R_{ta}(g)_a\) by
\(X_a\) on the old line, then evaluate at \(P_{t,a;a}\) and
divide by \(L_{Na}(P_{t,a;a})\). This divided residue is well
defined: if \(g=f/D_{\mathrm{old}}\in\mathcal N\), then
\(f_a\) vanishes at the matching old base point, and the other
old denominator factors are nonzero there. Thus its restriction to
the line has the factor \(X_a\).

All three \(\Gamma\) functionals vanish on \(W_m\). For
\(i\ne a\) this is the component's factor \(X_i\); for
\(i=a\), after dividing that factor, the remaining old coefficient
vanishes at its base point. They also vanish on the polynomial \(H_b\).
On the regular columns they give the diagonal-by-old-line blocks

\[
 \Gamma_{t,a;i}(C_{t,a,b})=A_t(a,b)(A_N^{-1})_{bi},
 \qquad
 \Gamma_{t,a;i}(C_{u,c,b})=0\quad((u,c)\ne(t,a)). \tag{S5}
\]

These three-by-three blocks are invertible. The \(H_b\) are
independent: if \(d=cA_N^{-1}\), the coefficient of \(X_j\),
\(j\ne i\), in component \(i\) of \(\sum_b c_bH_b\)
is \(d_iA_N(i,j)\), forcing \(d=0\) and \(c=0\).
Also \(W_m\) contains no nonzero homogeneous linear polynomial
row. Coprimality of each \(X_i\) and \(D_{\mathrm{old}}\)
would force such a row's components to be \(c_iX_i\), and row-sum
zero forces every \(c_i=0\). Hence the displayed sum is direct.
Its dimension is the previously established
\(\dim W_m+9m+3=\dim\mathcal N\), proving exhaustion.

These coordinates expose the graph terms of the transformed old source
columns. For old \(t,s\), and also for the single-block vectors,

\[
 F^B_{t,s,a,b}K_N^{-1}
       =F^{B\setminus\{N\}}_{t,s,a,b}+C_{t,a,b},
\]
\[
 E_{t,a}K_N^{-1}=E_{t,a}+H_a-\sum_b C_{t,a,b}. \tag{S6}
\]

Thus a long old source column's regular correction depends only on
\((t,a,b)\), independently of \(s\), whereas an old single-block
column has the correction \(-\sum_bC_{t,a,b}\). The latter
cannot be ignored merely because double residues discard single-block
columns. In particular, \(\Gamma\) by itself does not annihilate
the transformed old source space.

There is an exact correction after the old-old residues and the new
polar residues have been eliminated. By (S4), and the old canonical
basis whose double residues isolate every old local pair, the remaining
space is
\(\operatorname{span}\{E_{t,a},C_{t,a,b},H_b\}\).
For each old line its divided residue
\(r=\mathcal R_{ta}(g)/X_a\) is therefore a homogeneous linear
zero-sum row on that line. Put

\[
 \eta_i=\frac{r_i(P_{t,a;i})}{L_{Ni}(P_{t,a;i})},\qquad
 \gamma=\eta A_N.
\]

The row \(r-\sum_b\gamma_bH_b\) has component \(i\)
vanishing at \(X_i=0\) on the old line. Hence its components are
\(k_iX_i\) on that line; row-sum zero implies
\((k_i)_i=\lambda(A_t(a,i))_i\) for a unique scalar \(\lambda\).
Equivalently there is a unique decomposition

\[
 r=\sum_b\gamma_bH_b+\lambda v_{ta}.
\]

The resulting three regular coordinates are

\[
 \Delta_{t,a;b}(g)=\frac{\gamma_b}{A_t(a,b)}-\lambda.
 \tag{S7}
\]

They give the identity on the three columns \(C_{t,a,b}\), and
vanish on the new polynomial \(H_b\). For the transformed old
single-block column (S6), its divided residue is
\(-v_{ta}-\sum_b A_t(a,b)H_b\), so
\(\gamma_b/A_t(a,b)=-1\) and \(\lambda=-1\); (S7) therefore
vanishes as required. All evaluations and the extraction of \(\lambda\)
at a fixed nonzero component on the line are constant-linear operations.
The \(9m\) coordinates (S7) consequently give a complete coordinate
system on the remaining quotient by the transformed old single-block
columns and new polynomial columns. Applied after the eliminations in
(S1), they provide an equivalent description of the unresolved regular
matrix \(H\). No nonvanishing assertion for that source matrix
follows merely from this canonical coordinate lemma.

A proposed way to recover the old coefficient-sum incidence map from
axis-normal restrictions and one matching-basepoint normal jet per old
line fails. The observations are the complete functions
\((F_i/X_i)|_{X_i=0}\), represented by \(2m+1\) evaluations
per axis, together with the \(3m\) specified scalar jets. In
`exploration/source24_axis_jet_incidence.py` and
`exploration/source24-axis-jet-incidence-results.json`,
the \(m=3\) observation matrix has 30 rows while stacking the
incidence map underneath has rank 54; at \(m=4\) the corresponding
numbers are 39 and 75. The nonzero modular minors exceed the universal
observation row counts. After clearing the verified denominators, they
therefore certify nonfactorization over the reals at these rational
fixtures and generically, rather than merely a deficient modular rank.
This rules out that particular recovery of the incidence map. It does
not prove singularity of the regular matrix \(H\).

A simple absorbing-state limit also does not settle the determinant.
For \(G_h=((1,1,1),(1,2,4),(1,4,h))\), put
\(\varepsilon=h^{-1}\) and change effect coordinates to
\(X_2=\varepsilon Z\). In these coordinates the limiting coefficient
matrix is \(((1,1,0),(1,2,0),(1,4,1))\). After dividing each source
column by its nonzero scalar \(A_t(a,b)\), the limiting columns with
\(a,b\in\{0,1\}\) stay in the binary zero-sum direction: a chain
started in 0 or 1 cannot reach 2 at order zero. Their rational functions
depend only on \(X_1/X_0\), with a common product of \(2n\) binary
linear denominators and numerator degree \(2n+1\). Their span therefore
has dimension at most \(2n+2\), while there are \(4n(n-1)\) such
columns. The zeroth-order normalized family is necessarily deficient for
\(n\ge2\). This does not rule out a useful higher-order argument: at
first order a chain can enter state 2 and then propagate through additional
denominators involving \(Z\). No higher-order rank bound or nonvanishing
claim has been established for this degeneration.

## The leading regular operator at a small new time factor

The following conditional paper lemmas have passed an independent algebra
audit. Their incoming-operator formulas have also passed the separate
finite check described below. None of these statements proves generic
nonvanishing of the regular determinant for all lengths.

Use \(m\ge2\) old blocks \(A_t=G\operatorname{diag}(1,u_t,v_t)\),
where \(G\) has first column all ones, and put
\(A_N=G\operatorname{diag}(1,\varepsilon,\varepsilon^3)\).
Assume the old cross-points have nonzero coordinates, all old lines meet
\(X_0=0\) at distinct points with both other coordinates nonzero,
and the binary restrictions used below are invertible. Assume also that
the old residue matrix \(O=R_m\) is invertible. For the normalized
polar matrix, impose the conclusions established in the polar argument:
for odd \(m\) its constant term is invertible; for even \(m\)
its leading kernel is supported on initial states \(1,2\), and
the first kernel derivatives complete its rank. These hypotheses imply
that its inverse has at worst a simple pole, whose coefficient has zero
initial-state-zero rows.

There are two shared-new column normalizations to distinguish. Call
\(F_{N,s,a,b}/A_N(a,b)\) the **physical normalization** here.
The polar normalization divides this further by
\(\varepsilon^{[a=0]+[b=0]}\). Let \(\bar D,\bar P,\bar R\)
denote the blocks in physical normalization, and let
\(\lambda=\bar P^{-1}Q\). Transport the old-old residue rows by
\(K_N^{-1}\), so that their old block is the constant \(O\),
and divide beta row \((u,c,d)\) by its nonzero canonical factor
\(J_{ucd}=-A_u(c,d)X_c(P_{uc;N,d})X_d(P_{uc;N,d})\).
All blocks in the remainder of this section use these row conventions.

Here \(\lambda\) is analytic at \(\varepsilon=0\). To verify
this and the needed valuation bounds, choose the old-new cross-point
representatives analytically. Their coordinate zero is of order
\(\varepsilon\), while their other coordinates have nonzero limits.
The old residue vector \(U\) and the scaled new vector
\(V/\varepsilon\) form an invertible limiting basis of zero-sum
rows: their limits point along \((0,-1,1)\) and \((-1,1,0)\).
An old product residue has coordinate zero of order
\(\varepsilon\). Multiplying such a product or residue on the
left by \(V\) gives a row of order \(\varepsilon\), with
coordinate zero of order \(\varepsilon^2\). Consequently both
its \(U,V\) coordinates are of order \(\varepsilon\).

For a first-new source column \((t,N,A,B)\), the block \(Q\)
is supported on new line \(B\), and has order at least
\(\varepsilon^{1+[A=0]+[B=0]}\). Multiplying by the normalized
polar inverse and then undoing its column scaling proves analyticity
of \(\lambda\): its possible inverse pole is supported on the
binary initial states, whereas the extra factor for initial state zero
is canceled by the regularity of those inverse rows. Every physical
coefficient has order at least \([A=0]\).

The same cross-point calculation gives the direct beta bounds
\[
 \operatorname{val}(S)\ge0,\qquad
 \operatorname{val}(\bar R)\ge-1. \tag{H1}
\]
In detail, a beta row indexed by old state \(c\) and new state
\(a\) is divided by a factor of order \([c=0]+[a=0]\).
A shared-new column contributes order at least \([a=0]+[b=0]\),
so its resulting order is at least \([b=0]-[c=0]\).
A first-new column contributes order at least
\(1+[A=0]+[B=0]\), so its resulting order is at least
\(1+[A=0]-[c=0]\). These bounds include the matching old state
zero case; they do not assume that its vanishing coordinate is invertible
at the limit.

The normalized old-feedback block has the exact form
\[
 B_\varepsilon=J_{\rm inc}-T_\varepsilon,\qquad
 T_\varepsilon[(u,c,d),F]
 =\left.
 \frac{\operatorname{Res}_{L_{uc}}(F_d/X_d)}
      {A_u(c,d)X_c}\right|_{P_{uc;N,d}}, \tag{H2}
\]
where \(F\) is the shorter source column and \(J_{\rm inc}\)
adds its coefficients over the first slot at fixed shared labels.
The incidence term comes from the old-source graph identity preceding (S6).
The quotient in (H2) is regular at the matching coordinate base point:
the cleared coefficient polynomial of \(F_d/X_d\) vanishes there.
Thus \(B_\varepsilon\) is analytic, including old state zero.
At the common limiting point \(P_{uc}=\{L_{uc}=X_0=0\}\),
the three rows of \(T_0\) satisfy
\(\sum_d A_u(c,d)X_d(P_{uc})T_0[(u,c,d),F]=0\).
Hence \(\operatorname{rank}T_0\le6m\). This does not bound
\(B_0=J_{\rm inc}-T_0\) by \(6m\).

Put \(w=e_2G^{-1}\). At fixed old cross-points,
\[
 \varepsilon^3K_N^{-1}\longrightarrow
       (X_0/X_2)e_2w.
\]
Thus \(E,\bar D\) have valuation at least \(-3\). Define
\(Z=E-\bar D\lambda\). Equations (H1)--(H2) and analyticity
of \(\lambda\) give the exact leading-operator identity
\[
 H_{-3}=-B_0 O^{-1}Z_{-3}. \tag{H3}
\]
Indeed, \(H=S-\bar R\lambda-B_\varepsilon O^{-1}Z\),
and the first two terms have valuation at least \(-1\).
Every old cross-point residue in \(Z_{-3}\) is a scalar multiple
of the same row \(w\). In particular
\(\operatorname{rank}Z_{-3}\le9\binom m2\); no equality
or full-rank conclusion is implied.

For odd \(m\ge3\), the constant polar coefficients are explicit.
For a first-new column \((t,N,A,B)\), let
\(r=\min(\{1,\ldots,m\}\setminus\{t\})\), let
\(P^t\) be the ascending old product with \(t\) omitted,
and let \(P_r\) be the old move-\(r\)-first product.
Write \(d_t\) for the determinant of the binary restriction of
\(K_t\) on \(X_0=0\), and set
\[
 c_{t0}=0,\qquad
 c_{tA}=\left.\frac{X_A}{L_{tA}d_t}\right|_{X_0=L_{r0}=0}
 \quad(A=1,2). \tag{H4}
\]
Then \(\lambda_0\) is supported only at the shared-new column
\((N,r,B,0)\), where its coefficient is
\(A_t(A,B)c_{tA}\). Analyticity and invertibility of the odd
leading polar block make every physical binary coefficient vanish to
positive order. The remaining initial-zero coefficients are fixed by
their distinct old row-zero poles. Such a pole occurs only at the first
old transition, since every later transition has zero column zero on
the limiting axis. The first-new word starts at \(r\), while the
shared-new word with that pole contains the one extra block \(t\).
Its binary zero-sum residue is multiplied by \(d_t\), giving
exactly (H4). When \(A=0\), the extra vanishing source factor
instead gives \(\lambda_0=0\).

It follows that the \((t,A,B)\) column of \(Z_{-3}\) is the
old double-residue vector of
\[
 A_t(A,B)\frac{X_BX_0}{X_2}
 \left[-\frac{X_A}{L_{tA}}(P^t)_{02}
                +c_{tA}(P_r)_{02}\right]w. \tag{H5}
\]
The omitted identity terms have at most one old pole and therefore no
old double residues. Thus (H5) is a scalar rational interpolation
problem followed by the old source inverse and the explicit operator
\(B_0\); replacing that inverse by a new basis has not been justified.

The optional leading-operator diagnostic in
`exploration/source24_regular_laurent.py` checks (H3)--(H5) entrywise
at its \(m=3\), \(G_{30}\) fixture. There
\(\operatorname{rank}B_0=27\),
\(\operatorname{rank}(B_0-J_{\rm inc})=18\), and
\(Z_{-3}\), \(O^{-1}Z_{-3}\), and
\(B_0O^{-1}Z_{-3}\) all have rank 21 modulo the test prime.
The six missing leading directions therefore already occur in the
incoming matrix in that finite calculation. The support bound proved
below supplies the characteristic-zero upper bound at \(m=3\);
no all-length parity rule follows.

### Scalar interpolation and an exact incoming recurrence

There is a useful scalar quotient behind (H5). Assume that the old
denominator lines are distinct, no three meet, their cross-block
intersections have nonzero coordinates, and every coordinate base point
\(L_{ta}=X_a=0\) is on no other denominator line. Let
\(D=\prod_{t,a}L_{ta}\), and let \(Z_{\rm old}\) consist of
the within-block line-pair points and the coordinate base points.
Consider the scalar degree-one rational space
\[
 \mathcal S_m=\{q/D:q\in I(Z_{\rm old})_{3m+1}\}.
\]
Its subspace with no cross-block double residues is exactly
\[
 \mathcal U_m=\mathbb R[X]_1+
 \sum_{t,a}\left\{q_{ta}/L_{ta}:q_{ta}\in\mathbb R[X]_2,
                    \ q_{ta}|_{L_{ta}=X_a=0}=0\right\}. \tag{H6}
\]
Moreover, one basis element of \(\mathcal S_m/\mathcal U_m\)
for each unordered cross-block line pair is
\[
 \frac{X_aX_bX_0}{L_{ta}L_{sb}},\qquad t<s. \tag{H7}
\]
Each displayed function belongs to \(\mathcal S_m\), has no
other cross-block double residue, and its residue at its own pair is
nonzero. To prove exhaustion, subtract these pair residues from any
\(q/D\). The remaining residue on each old line has no poles:
cross-block poles have been removed, and the numerator's vanishing at
within-block intersections excludes the other possible poles. This
residue is therefore a homogeneous quadratic on that projective line.
It vanishes at the matching coordinate base point, so lift it to an
allowed \(q_{ta}\) in (H6) and subtract \(q_{ta}/L_{ta}\).
After all residues are removed, the remainder is a linear polynomial.
This proves both (H6) and the basis assertion, in particular
\(\dim(\mathcal S_m/\mathcal U_m)=9\binom m2\).

The scalar functions in (H5) lie in this space for a direct reason.
Write \(F_{r,0}=X_0e_0(I-P_r)\) for the old zeroth-level
word, and let \(F_{t,r,A,0}\) be its indicated old first-level
source. Component two of the exact identity
\[
 X_0\left[-\frac{X_A}{L_{tA}}e_0P^t+c_{tA}e_0P_r\right]
 =\frac{F_{t,r,A,0}}{A_t(A,0)}-c_{tA}F_{r,0}
   +X_0\left(c_{tA}-\frac{X_A}{L_{tA}}\right)e_0 \tag{H8}
\]
has no contribution from the final term. The old moment-space property
therefore writes that component as \(X_2 g_{tA}/D\), with
\(g_{tA}\in I(Z_{\rm old})_{3m}\). The incoming scalar
numerator is exactly \(A_t(A,B)X_Bg_{tA}\). Thus the remaining
incoming-rank question is a degree-one polynomial multiplication map
followed by the quotient (H6). Multiplication by \(X_B\) is part
of this map; it is not an allowed constant column change or a reason
to transfer independence from the unmultiplied functions.

For an exact recurrence, define the row
\[
 V_{tA}^{(m)}=-\frac{X_A}{L_{tA}}e_0P^{m\setminus\{t\}}
                         +c_{tA}e_0P_r^{m}.
\]
This auxiliary definition makes sense for every \(m\ge3\),
although (H5) identifies it with the leading incoming operator only
for odd \(m\). On appending a largest block, the constants
\(r,c_{tA}\) of every existing column stay fixed, and
\[
 V_{tA}^{(m+1)}=V_{tA}^{(m)}K_{m+1}\qquad(t\le m). \tag{H9}
\]
At an old cross-point its double residue is a zero-sum row, since
the row sum of \(V_{tA}\) is \(-X_A/L_{tA}+c_{tA}\),
which has only one pole. A fixed coefficient relation whose selected
component two vanishes can consequently have a nonzero vector residue
proportional to \(e_0-e_1\). Appending a generic block need not
preserve it: its new component is multiplied by
\[
 (K_{m+1})_{02}-(K_{m+1})_{12}
 =\frac{vX_2\bigl[(G_{02}-G_{12})X_0+
          (G_{02}G_{11}-G_{12}G_{01})uX_1\bigr]}
        {L_{m+1,0}L_{m+1,1}}. \tag{H10}
\]
At an old cross-point this is not identically zero in \(u,v\)
when \(G\) is invertible and \(G_{02},G_{12}\ne0\), as in
the positive parameter family. This observation concerns fixed
coefficient relations. It does not exclude new parameter-dependent
relations and therefore does not prove a generic rank increase.

There is also an exact support restriction. All four incoming scalar
rows at
\(L_{1c}=L_{2d}=0\), \(c,d\in\{1,2\}\), vanish.
For \(t>1\), both words in (H5) start at block one in state
zero, so their only block-one denominator is \(L_{10}\).
For \(t=1\), both words start at block two in state zero, so
their only block-two denominator is \(L_{20}\). The shared pole
is then in block one. More strongly, all \(6(m-1)\) scalar
pair rows involving \(L_{11}\) or \(L_{12}\) are supported
on only the six columns \(t=1,A\in\{1,2\},B\in\{0,1,2\}\).
The \(t=1,A=0\) columns have only their shared pole \(L_{10}\),
since \(c_{10}=0\). This entire row block therefore has rank at
most six. Adding all remaining scalar pair rows proves, for odd
\(m\ge3\),
\[
 \operatorname{rank}Z_{-3}\le
 \min\!\left(9m,\;9\binom m2-6m+12\right). \tag{H11}
\]
At \(m=3\) this is the characteristic-zero upper bound 21,
stronger than the bound 23 obtained from only the four zero rows.
The recorded nonzero modular minor of size 21 lifts after denominator
clearing, so the incoming rank is exactly 21 at that rational fixture
and generically in the common-\(G\), independent-time family.
Equation (H3) bounds the corresponding leading regular rank by 21,
and its recorded nonzero mapped minor gives generic equality as well.
This proves a six-dimensional generic leading kernel at \(m=3\).
It does not force a deficit at any larger odd length or imply that the
full Laurent regular matrix is singular.

This also upgrades two finite Laurent orders to characteristic-zero
statements. The entry bound \(\operatorname{val}(H)\ge-3\)
and the \(m=3\) bound \(\operatorname{rank}H_{-3}\le21\)
give
\(\operatorname{val}\det H\ge-3\cdot27+6=-75\):
after a constant column change, at least six columns of
\(\varepsilon^3H\) are divisible by \(\varepsilon\).
The precision-tracked result in
`exploration/source24-regular-laurent-results.json` has nonzero
coefficient 899455 modulo 1000003 at order \(-75\), with the
required denominator reductions valid. Thus the determinant order is
exactly \(-75\) over the rationals at that \(m=3\) fixture.
At \(m=4\), the full leading rank 36 and the same entry bound
give exact rational determinant order \(-108\), whose recorded
leading coefficient is 359304 modulo the prime. These use the existing
precision-certified calculations in
`exploration/source24_regular_laurent.py`; no new computation or Lean
valuation theorem is asserted. The recorded \(m=2\) order \(-24\)
remains a finite-field order because a matching characteristic-zero
lower bound has not been established there.

### Six boundary pivots for every auxiliary length at least five

The scalar quotient, recurrence, support bound, and six-pivot proof in
this subsection and the preceding one have passed an independent algebra
audit. The six-pivot statement concerns the auxiliary family for every
\(m\ge5\), and the actual leading incoming matrix for odd
\(m\ge5\).

There is an exact appended-column identity before any rank argument.
For linear forms \(q_{tA}=\sum_B\mu_{tAB}X_B\), let
\(U=\sum_{t\le m,A}q_{tA}V_{tA}^{(m)}\),
\(P=e_0P^{\{1,\ldots,m\}}\), and
\(C=\sum_A c_{NA}q_{NA}\), where \(N=m+1\).
The combined auxiliary incoming row is
\[
 (U+CP)K_N-P\sum_A\frac{q_{NA}X_A}{L_{NA}}.
\]
Its selected component is therefore
\[
 \sum_c\frac{A_N(c,2)X_2(U_c+CP_c)-q_{Nc}X_cP_2}{L_{Nc}}.
 \tag{H12}
\]
This does not remove the old inverse or prove independence of the new
columns. It displays explicitly what their old-new residues must cancel.

A bounded part of the incoming family can nevertheless be isolated
uniformly. Fix a positive invertible \(G=(\mathbf1,\alpha,\beta)\)
with the binary and coordinate-edge nondegeneracy assumptions used in
(H4). For every \(m\ge5\), the six auxiliary scalar columns
\(t=1,A\in\{1,2\},B\in\{0,1,2\}\) have a nonzero
minor using only pair rows involving \(L_{11}\) or \(L_{12}\).
All other incoming columns vanish on these rows by the support argument
above. This proves six generic pivots, including for the odd lengths
where (H5) is the leading regular operator; it leaves the other
\(9m-6\) columns unresolved.

Here is a parameter-only leading-minor proof. Divide the six columns by
\(A_1(A,B)\), write their constant combination using linear forms
\(q_1,q_2\), and put
\(\kappa_A=c_{1A}\), \(C=\kappa_1q_1+\kappa_2q_2\).
On \(L_{1c}\), \(c=1,2\), its residue is
\[
 \frac{X_0X_c}{L_{20}X_2}
   [-q_c v_{20}+C A_2(0,c)v_{1c}]
                       K_3W e_2,\qquad W=K_4\cdots K_m. \tag{H13}
\]
Keep all blocks except three fixed and set
\((u_3,v_3)=\delta(u_*,v_*)\), with \(u_*,v_*>0\).
At the six selected cross-points, which do not involve block three,
\(K_3=\mathbf1e_0+\delta M_3+O(\delta^2)\), where
for a zero-sum row \(h\),
\[
 hM_3=u_*\frac{X_1}{X_0}(h\alpha)(e_1-e_0)
             +v_*\frac{X_2}{X_0}(h\beta)(e_2-e_0). \tag{H14}
\]
This is invertible on zero-sum rows: \(G\) is invertible and all
displayed coordinate factors are nonzero.

The constant term of (H13) is
\(-X_0X_cq_c(e_0We_2)/X_2\), since
\(v_{20}\mathbf1=L_{20}\) and
\(v_{1c}\mathbf1=0\) on its line. For each \(c\), take
the two pair rows against \(L_{40}\) and \(L_{50}\).
Their leading values are nonzero scalar multiples of the evaluations
of \(q_c\) at two distinct points of \(L_{1c}\).
Indeed, the relevant residues of \(e_0W\) are
\(v_{40}K_5\cdots K_m\) and
\((K_4)_{00}v_{50}K_6\cdots K_m\), respectively.
They have nonzero component two generically. In the second expression
with \(m=5\), this is immediate from \((v_{50})_2\ne0\).
In every other case the intervening kernels are invertible at the
point, and a generic last transition detects any nonzero row: its
component-two column consists of nonzero constants divided by three
distinct affine denominator forms in its time parameters. These three
reciprocal forms are linearly independent over constants, as is seen by
restricting to each one's pole. The remaining coefficient
\((K_4)_{00}=X_0/L_{40}\) is nonzero at the second point.

The resulting four leading pivots have constant kernel
\(q_1=k_1L_{11}\), \(q_2=k_2L_{12}\).
This is an allowed column kernel: the coefficients of each \(L\)
are parameter-only constants. Take the last two rows against
\(L_{20}\), one on each \(L_{1c}\). Every leading column
vanishes on these rows, because its factor \(L_{20}\) canceled
in the preceding constant term. On the two-dimensional kernel, their
first coefficients are
\[
 \left.\frac{X_0X_c}{X_2}C A_2(0,c)
                      v_{1c}M_3W e_2\right|_{L_{1c}=L_{20}=0}.
 \tag{H15}
\]
Here \(C=\kappa_2k_2L_{12}\) on \(L_{11}\), while
\(C=\kappa_1k_1L_{11}\) on \(L_{12}\). The coefficient
matrix in \(k_1,k_2\) is therefore antidiagonal with generically
nonzero entries. Both \(\kappa_A\) are nonzero by (H4), and
\(v_{1c}M_3\ne0\) by (H14); the same last-transition argument
makes its final component nonzero generically. Because these two rows
are zero on the entire leading matrix, no removal of the four leading
pivots can cancel the two displayed first-order pivots.

All generic choices just used are finitely many nonzero rational
conditions on the common-\(G\) time parameters. Each nonzero factor
has the independent witness argument above; their nonzero sets therefore
intersect in the positive parameter domain. The selected minor has a
nonzero coefficient at order \(\delta^2\) after a constant
column change, and is nonzero for sufficiently small positive
\(\delta\). This is a six-column result, not a determinant
argument for the full incoming or regular matrix.

The separate exact modular script `exploration/source24_odd_incoming.py`
and `exploration/source24-odd-incoming-results.json` check the direct
operator without a Laurent expansion. At the \(G_{30}\) fixtures,
the scalar incoming matrix and its actual image
\(B_0O^{-1}Z_{-3}\) both have full ranks 45 for \(m=5\)
and 63 for \(m=7\). The old source matrix itself is assembled,
and its solve is checked by \(OY=Z_{-3}\); it is not replaced
by a canonical source basis. The odd polar hypotheses and relevant
geometry are verified at these fixtures. At \(m=3\), both the
economic-time and an independent-time fixture have scalar and mapped
rank 21, while the full vector residue matrix before selecting the
output component has rank 27, all modulo the test prime. The latter
distinction supports the need to track the changing projection in (H9).
Together with (H11), the nonzero scalar and mapped minors establish
the stated generic rank 21 in characteristic zero at \(m=3\).

The script also finds a full six-by-six boundary minor at each of
\(m=3,5,7\), using first-block states \(1,2\) crossed with
all three states of the last old block. Every other incoming column
vanishes on those rows. These finite minors use different rows from
the uniform proof (H13)--(H15), which uses blocks two, four, and five
and starts at \(m=5\). None of the finite checks establishes an
arbitrary-length incoming or mapped determinant.

There is a precise open reduction after the six coefficients in the
first block have been removed. Write \(P_{\rm tail}=K_2\cdots K_m\).
Multiplying the remaining combined row by \(L_{10}\) gives
\[
 -q_{10}X_0e_0P_{\rm tail}
 +v_{10}\sum_{t\ge2,A}q_{tA}
       \left[-\frac{X_A}{L_{tA}}P_{{\rm tail}\setminus\{t\}}
                         +c_{tA}P_{\rm tail}\right]. \tag{H16}
\]
If \((u_1,v_1)=\delta(u_*,v_*)\) with fixed positive ratio,
the points defining \(c_{tA}\) stay fixed. Dividing (H16) by
\(X_0\) and taking its constant term yields
\[
 e_0\left[\ell(X)P_{\rm tail}
       -\sum_{t\ge2,A}q_{tA}(X)\frac{X_A}{L_{tA}}
                             P_{{\rm tail}\setminus\{t\}}\right],
 \qquad \ell=\sum_{t\ge2,A}c_{tA}q_{tA}-q_{10}. \tag{H17}
\]
Here \(\ell\) is an arbitrary linear form, giving a deletion-word
family with three additional common-word columns. This is not the
previous auxiliary family: for the first shared block in the tail,
that family would use a different move-first correction. The following
induction proves its generic independence. Simple pole removal
alone does not resolve it: taking \(q_{tA}\) proportional to
\(L_{tA}\) removes its shared pole while leaving a linear-form
multiple of a deleted product.

### Deletion-word induction and incoming-rank corollary

**Status: independently audited paper proof; not formalized in Lean.** The argument
below uses the saved exact finite-field minor only as a characteristic-zero
base case. Its induction is symbolic. It does not prove the remaining
\(B_0O^{-1}\) transversality, a full regular determinant, or independence
of the specified source family for every length.

Renumber the blocks \(1,\ldots,k\), and let \(\mathcal D_k\) be
the scalar cross-block double-residue matrix of
\[
 \mathcal R_k(\ell,q)
 =\ell(X)e_0K_1\cdots K_ke_2
  -\sum_{t=1}^k\sum_{A=0}^2q_{tA}(X)\frac{X_A}{L_{tA}}
                  e_0P^{\widehat t}e_2. \tag{D1}
\]
All \(\ell,q_{tA}\) are arbitrary homogeneous linear forms, so
there are \(9k+3\) constant real coefficients. Every deleted word
\(P^{\widehat t}\) is in ascending order. The parameters are one
common normalized matrix \(G\), with first column all ones, and
independent time factors \(A_t=G\operatorname{diag}(1,u_t,v_t)\).
The conclusion is that \(\mathcal D_k\) has generic full
column rank for every \(k\ge4\).

All genericity statements refer to nonzero polynomials on this same
parameter space. We impose distinct old lines, no unintended triple
intersections, nonzero effect coordinates at cross-block intersections,
and distinct old intersections with \(X_0=0\). We also require
\(G\) invertible, its entries nonzero, and
\(\det G_{\{1,2\},\{1,2\}}\ne0\). These are open conditions;
the degeneration used below is allowed to leave the line-geometry open
set at its limiting parameter, while all matrices used for the induction
extend analytically in the specified residue coordinates.

First, rows involving \(L_{11}\) or \(L_{12}\) see only the
corresponding shared-block term \(q_{1c}X_c/L_{1c}\), \(c=1,2\).
Every other word starts block one in state zero or omits that block.
For each \(c\), use its intersections with \(L_{20}\) and
\(L_{30}\). The residues of \((K_2\cdots K_k)_{02}\) there
are generically nonzero: they contain respectively
\(v_{20}K_3\cdots K_ke_2\) and
\((K_2)_{00}v_{30}K_4\cdots K_ke_2\).
The two distinct points detect a linear form restricted to
\(L_{1c}\). Consequently four boundary pivots reduce any residue
relation to
\[
 q_{11}=aL_{11},\qquad q_{12}=bL_{12}, \tag{D2}
\]
where \(a,b\) are constants. Equivalently, use the coefficient
basis \(X_1,X_2,L_{1c}\) for each of these two forms. Its change
of coordinates is invertible because the coefficient of \(X_0\)
in \(L_{1c}\) is one. The four boundary rows are identically
zero on the remaining columns. No effect-dependent column operation
is used.

Now set
\[
 (u_1,v_1)=\delta(u_*,v_*),\quad
 h=(0,G_{01}u_*X_1,G_{02}v_*X_2),\quad l=h_1+h_2,
 \quad s=aX_1+bX_2,
\]
so \(v_{10}=X_0e_0+\delta h\) and
\(L_{10}=X_0+\delta l\). Write
\(P=K_2\cdots K_k\) and
\(Q=\sum_{t\ge2,A}q_{tA}X_A/L_{tA}\,P^{\widehat t}_{\rm tail}\).
After (D2), the remaining row before taking its final component is
\[
 \frac{(X_0e_0+\delta h)(\ell P-Q)
              -(q_{10}X_0+sL_{10})e_0P}{L_{10}}. \tag{D3}
\]
Use the invertible constant coefficient change
\(\ell'=\ell-q_{10}-s\). At \(\delta=0\), (D3) is
\(e_0(\ell'P-Q)\): the smaller deletion family on the tail,
plus five zero columns parametrized by \(q_{10},a,b\).
If \(\mathcal D_{k-1}\) has full rank, this is exactly the
constant kernel of the leading residue matrix. On that kernel,
(D3) is exactly
\[
 \frac{\delta}{L_{10}}
       \big[(q_{10}+s)h-sl e_0\big]P. \tag{D4}
\]

Choose the following five residue rows in addition to any full smaller
deletion minor:
\[
 \begin{split}
 &L_{10}\cap L_{20},\quad L_{10}\cap L_{21},\quad
 L_{10}\cap L_{22},\quad L_{10}\cap L_{31},\qquad
 L_{21}\cap L_{31}. \tag{D5}
 \end{split}
\]
They are zero on the entire leading smaller family. The first four
are new-line rows. For the fifth, both first-two-tail-block states
are nonzero. A smaller common word starts block two in state zero;
a deletion/shared term either also does so, or deletes block two
and starts block three in state zero. Thus no smaller deletion column
has this double residue.

Here are the regularity and normalization details for this first-jet
argument. Choose projective representatives with \(X_1=1\) in
(D5); this is possible generically and amounts to nonzero, parameter-only
row scalings relative to homogeneous cross-product representatives.
All old-tail rows have \(X_0\ne0\), so (D3) is analytic there.
On a new-line row, multiply by \(L_{10}\) before evaluating its
old-line residue. The numerator in (D3) has zero constant term at
\(L_{10}=X_0=0\), and all other old denominators are nonzero at
the selected point. Thus these rows also extend analytically and
have zero constant coefficient. The canceled lines \(L_{11},L_{12}\)
do not occur in (D3), so their coalescence with \(X_0\) produces
no additional pole. In (D4) the explicit factor \(\delta\) means
the first coefficient is evaluated at \(X_0=0\); motion of the
cross-point contributes only at higher order. The four earlier boundary
pivots are used at finite generic \(\delta\), and need no regular
limit of their own.

Put \(p=(q_{10}+s)|_{X_0=0}\), a binary linear form. On the
first four rows of (D5), the kernel derivative is the indicated
old-line residue on \(X_0=0\) of
\[
 p\big[h_1P_{12}+h_2P_{22}\big]-slP_{02}. \tag{D6}
\]
At \(L_{21}\) and \(L_{22}\), only the corresponding first
term has a pole; their nonzero factors force \(p\) to vanish
at two distinct axis points, hence \(p=0\). At \(L_{20}\)
and then \(L_{31}\), the remaining expression forces \(s\)
to vanish at two distinct points, hence \(s=0\). The latter
pole is state one, not state zero: after the first tail transition,
state zero is unreachable on this axis. Explicitly its residue in
\(P_{02}\) contains
\((K_2)_{01}v_{31}K_4\cdots K_ke_2\), which is nonzero
generically. The first four kernel-jet rows therefore have rank four,
with remaining kernel
\[
 q_{10}=cX_0,\qquad a=b=0. \tag{D7}
\]
All nonzero factors just used are explicit: \(h_1,h_2\), the two
selected values of \(l\), nonzero transition entries, and propagated
binary zero-sum residues. On \(X_0=0\), the nonzero binary minor
of \(G\) makes every subsequent binary kernel invertible on its
one-dimensional zero-sum subspace. The values of \(l\) can be
kept nonzero by choosing the positive ratio \(u_*/v_*\) away
from finitely many exceptional values.

For (D7), (D4) equals
\(c\delta X_0/L_{10}\,hP\), so its first derivative on an
old-tail row is \(c hP\). On the fifth row of (D5), its residue
is
\[
 c\,h_1 A_2(1,1)X_1\,
                (v_{31}K_4\cdots K_k)_2
       \big|_{L_{21}=L_{31}=0}. \tag{D8}
\]
This is generically nonzero. The first factors are nonzero by the
cross-point assumptions. The nonzero zero-sum row \(v_{31}\)
survives the invertible intermediate kernels. The final block \(k\)
is distinct from blocks two and three when \(k\ge5\); varying
its two time factors detects any such nonzero row. Indeed its output-two
entries are nonzero multiples of three distinct reciprocal linear
denominators in those factors. A rational linear combination of them
cannot vanish identically unless all coefficients vanish, as is seen
by isolating each denominator pole. This proves nonvanishing on the
same common-\(G\) parameter space, rather than on a space of freely
varying transition matrices.

Order the five kernel coordinates by the two coefficients of \(p\),
the two coefficients of \(s\), and the coefficient of \(X_0\)
in \(q_{10}\). The rows \(L_{21},L_{22}\) first give an
invertible two-by-two evaluation block for \(p\). After eliminating
them, rows \(L_{20},L_{31}\) give such a block for \(s\).
The last diagonal entry is (D8). Hence the five-by-five first-kernel
matrix is invertible. The selected full reduced minor has leading
coefficient
\[
 \delta^5\det(\text{smaller deletion minor})
                   \det(\text{five kernel-jet rows}), \tag{D9}
\]
up to a nonzero constant sign. This is ordinary constant-kernel
column elimination: each of the five new rows vanishes on the whole
leading matrix. No independent stacking of derivatives is involved.
Restoring the four boundary pivots from (D2) proves the
implication
\(\mathcal D_{k-1}\text{ full}\Longrightarrow\mathcal D_k\text{ full}\)
for \(k\ge5\).

To combine the required nonzero factors, clear their denominators.
The tail determinant, the boundary factors, and the kernel-jet factors
are each nonzero polynomials on the irreducible common-\(G\),
independent-time parameter space. Their product is nonzero. Its open
set intersects the positive parameter orthant; choose a point there,
then a sufficiently small positive \(\delta\). All remaining
generic line conditions can also be imposed at finite \(\delta\).
This justifies intersecting the separate nonvanishing arguments without
requiring their preliminary witness points to coincide.

The base dependency is explicit. In
`exploration/source24_deletion_word.py` and
`exploration/source24-deletion-word-results.json`, the \(k=4\)
matrix has a saved 39-by-39 minor equal to \(621903\) modulo
\(1000003\), with every denominator used by the residue construction
nonzero modulo that prime. Its rational parameters are
\[
 G=\begin{pmatrix}1&1&1\\1&30&10\\1&3&2\end{pmatrix},\qquad
 (u_t,v_t)=(8^t,8^{2t}),\quad t=1,2,3,4.
\]
Thus this rational minor is nonzero in characteristic zero. The
induction gives full rank \(9k+3\) for every
\(k\ge4\). The separate \(k=5\) rank-48 minor is a finite
check, not an additional induction assumption.

For comparison, the \(k=3\) deficiency has a structural upper
bound. The \(6(k-1)\) rows involving \(L_{11}\) or \(L_{12}\)
depend on only the two restrictions \(q_{11}|_{L_{11}}\),
\(q_{12}|_{L_{12}}\), together of dimension four. Therefore
\[
 \operatorname{rank}\mathcal D_k\le
 \min\!\left(9k+3,\;9\binom k2-6k+10\right). \tag{D10}
\]
At \(k=3\), the saved nonzero 19-minor and this upper bound give
generic characteristic-zero rank exactly 19. In the pole-removal
subspace \(q_{tA}=k_{tA}L_{tA}\), the three explicit kernel
functions are nonzero multiples of
\(L_{20}(K_2K_3)_{02}\),
\(L_{10}(K_1K_3)_{02}\), and
\(L_{10}(K_1K_2)_{02}\). Each has only single-block poles after
canceling its first row-zero denominator. They are quotient relations,
not rational-function zero identities; the full 11-dimensional
\(k=3\) residue kernel is larger.

Finally, (H17) proves independence of
the remaining \(9m-6\) incoming columns for every odd \(m\ge5\):
put \(k=m-1\), and use the invertible coefficient map
\(\ell=\sum c_{tA}q_{tA}-q_{10}\). At tail-tail cross-points,
the degeneration in (H16)--(H17) and the incoming common factor only
apply nonzero parameter-only row scalings. The six columns already
handled by (H13)--(H15) are isolated by rows involving \(L_{11}\)
or \(L_{12}\), on which all remaining columns vanish identically.
Their minor and a remaining-column minor therefore combine in a block
triangular matrix. Their separately nonzero polynomials can be
intersected on the common parameter space. The resulting corollary is
generic full rank \(9m\) of \(Z_{-3}\) for odd \(m\ge5\),
subject to the earlier polar hypotheses identifying the auxiliary
family with the actual incoming operator. It does not show that
\(B_0O^{-1}\) is injective on this image. That is still the
remaining transversality problem in the leading regular operator.

The inverse-map hypothesis should be separated from this incoming result.
The deletion theorem and the auxiliary incoming-rank argument do not use
\(O\). Identifying the auxiliary family with \(Z_{-3}\) by (H5)
uses the odd polar inverse and (H4), but likewise does not require
\(O\) to be invertible. Old-source invertibility enters only when
forming \(O^{-1}Z_{-3}\) and applying (H3). Thus the new incoming
nonvanishing statement is not conditional on already proving the old
source independence.

### Feedback on the unmultiplied auxiliary rows

The following paper calculation has passed both the primary researcher's
check and a separate independent audit; it is not formalized in Lean. It describes
the \(3m\) old moment rows underlying (H8), not the actual
\(9m\)-column incoming image. Define, for \(m\ge3\),
\[
 U_{tA}=F_{t,r,A,0}/A_t(A,0)-c_{tA}F_{r,0},\qquad
 r=\min(\{1,\ldots,m\}\setminus\{t\}). \tag{U1}
\]
Here \(F_{r,0}=X_0e_0(I-P_r)\) is the long zeroth-level word,
and \(E_{r,0}=X_0e_0(I-K_r)\) is the local single-block row.
Our normalized common-\(G\) family has \(A_t(A,0)=1\).

Extend the incidence map to local singles by
\(J_{\rm inc}(E_{u,c})=-\sum_{d=0}^2e_{(u,c,d)}\).
The feedback map satisfies the identical formula on these rows:
\(T_0(E_{u,c})=-\sum_{d=0}^2e_{(u,c,d)}\), directly from
\(\operatorname{Res}_{L_{uc}}E_{u,c}=-X_cv_{uc}\).
Thus \(B_0(E_{u,c})=0\). In particular the correction applies
to **all three output indices**, not only output zero. If
\(s=\min(\{1,\ldots,m\}\setminus\{r\})\), the exact identity
\[
 F_{r,0}=E_{r,0}+\sum_{b=0}^2F_{r,s,0,b}
\]
gives \(J_{\rm inc}(F_{r,0})=0\). Hence
\(J_{\rm inc}(U_{tA})=e_{(t,A,0)}\).

All binary-output rows of \(T_0(U_{tA})\) vanish. To check this,
let \(P_{r0}=\{X_0=L_{r0}=0\}\), with a fixed projective
representative, and evaluate all the following binary determinants
at that point. For output \(d=1,2\), the only potentially
nonzero feedback row of either constituent in (U1) is \((r,0,d)\).
Every other row retains a factor \(X_0\), including a later
visit to state zero. At the first row-zero pole the two values are
\[
 -\frac{X_A}{L_{tA}}\prod_{j\ne r,t}d_j,
 \qquad -\prod_{j\ne r}d_j,
\]
respectively. Equation (H4) cancels them. Therefore
\(J_{\rm inc}(U_{tA})\) and \(T_0(U_{tA})\) both have zero
binary-output rows, and so does \(B_0(U_{tA})\).

For output zero, the direct incidence term cancels the simple
\(X_A/L_{tA}\) term. The remaining exact expression is
\[
 B_0[(u,c,0),U_{tA}]
 =\left.
  \frac{\operatorname{Res}_{L_{uc}}
    \left[(X_A/L_{tA})(P^t)_{00}-c_{tA}(P_r)_{00}\right]}
       {X_c}\right|_{X_0=L_{uc}=0}. \tag{U2}
\]
The matching division by \(X_c\) uses the regular extension
already established in (H2). If \(c\ne0\), the final output
zero supplies an uncanceled factor \(X_0\), so (U2) vanishes.
If \(c=0\), divide by that factor first. A product then has a
row-zero pole only at its first block: an intermediate transition
into state zero would supply a second factor of \(X_0\). Thus
only \(u=r\) can remain. When \(t<m\), both words have the
same last block \(m\). Their first-pole normal residues differ
by the binary determinant \(d_t\), canceled again by (H4).
When \(A=0\), its extra factor \(X_A=X_0\) also makes the
remaining expression zero. Consequently
\[
 B_0(U_{tA})=0\quad(t<m\text{ or }A=0),\qquad
 \operatorname{supp}B_0(U_{mA})\subseteq\{(1,0,0)\}.
 \tag{U3}
\]

There is an explicit formula for the possible surviving entry. Fix
the point \(P_{10}=\{X_0=L_{10}=0\}\), and evaluate every
quantity in the next display at this same point. Put
\(\theta_j=1/L_{j1}-1/L_{j2}\). Stripping the last transition
before taking its output-zero normal component gives
\[
 B_0[(1,0,0),U_{mA}]
 =\frac{X_A}{L_{mA}}(v_{10})_1
     \left(\prod_{j=2}^{m-1}d_j\right)
      \left[\frac{\theta_{m-1}}{d_{m-1}}
                        -\frac{\theta_m}{d_m}\right]. \tag{U4}
\]
Write \(\alpha_i=G_{i1}\), \(\beta_i=G_{i2}\), and
\(\Delta=\alpha_1\beta_2-\alpha_2\beta_1\ne0\). On the
axis,
\[
 \frac{\theta_j}{d_j}
 =\frac1\Delta\left[
    \frac{\alpha_2-\alpha_1}{v_jX_2}
       +\frac{\beta_2-\beta_1}{u_jX_1}\right]. \tag{U5}
\]
The bracket in (U4) is therefore generically nonzero for independent
time factors. The common-\(G\) feedback matrix on the \(3m\)
columns \(U_{tA}\) has generic rank exactly one. This is a
symbolic support and nonvanishing statement, not merely a deficient
modular computation.

The separate finite check
`exploration/source24_auxiliary_feedback.py`, with results in
`exploration/source24-auxiliary-feedback-results.json`, verifies
the extended incidence convention, \(B_0=J_{\rm inc}-T_0\),
and the support/rank assertion at \(m=3,5\), for both independent
and economic time factors with \(G_{30}\). Each case has rank
one, supported only at \((1,0,0)\) and the two columns
\((m,1),(m,2)\).

This does not give a rank bound for the incoming or mapped matrices.
By (H8), the actual incoming column is the double-residue vector of
\[
 A_t(A,B)\frac{X_B}{X_2}(U_{tA})_2\,w. \tag{U6}
\]
Selecting component two, multiplying by \(X_B/X_2\), and replacing
its row direction by \(w\) are not constant coefficient changes
of the old source columns. Their effects on \(B_0O^{-1}\) are
precisely what remains to be controlled. The rank-one result rules
out bypassing that operation by applying \(B_0\) directly to
the unmultiplied auxiliary rows.

## A proved bridge to scalar covariates

One need not insist on slopes \((0,1,2)\) when searching for a generic
economic witness. The following elementary specialization lemma removes
that unnecessary restriction.

Let \(P(G,u_1,v_1,\ldots,u_n,v_n)\) be a nonzero polynomial obtained by
clearing the residue determinant's denominators on matrices
\(A_t=G\operatorname{diag}(1,u_t,v_t)\), with the normalized entries of
\(G\) treated as parameters. Choose an integer \(B\) strictly larger
than the degree of \(P\) in each individual \(u_t\). Then

\[
 P(G,u_1,u_1^B,\ldots,u_n,u_n^B)
\]

is a nonzero polynomial. Indeed, each monomial's pair of exponents
\((a_t,b_t)\) maps to \(a_t+Bb_t\); the bound \(0\le a_t<B\) makes
this map injective in every time coordinate. Distinct monomials cannot
cancel under substitution. A nonzero real polynomial cannot vanish on
the entire positive orthant, so positive normalized \(G\) and positive
\(u_t\) can be selected off its zero set. Taking \(x_t=\log u_t\) and
slopes \((0,1,B)\) realizes these tables with a scalar covariate.

The same argument can be applied to the product of this determinant
numerator and any finite list of required nonzero geometry polynomials,
provided that product is nonzero in the common-\(G\), independent-time-factor
family. This proves economic attainability once nonvanishing has been
shown on that intermediate family. It does not turn a result for freely
varying transition tables into a result for a common \(G\); that remains
a substantive restriction.

Finite-field deficiency alone does not establish a real rank upper bound.
For the original conic \(T=5\) witness, however, a subsequent exact
rational calculation now establishes

\[
 \operatorname{rank}_{\mathbb Q}R_3=51,\qquad
 \dim_{\mathbb Q}\ker R_3=3.
\]

The calculation verifies three primitive integer nullvectors against the
original rational matrix; a nonzero modular minor supplies the matching
rank lower bound. Their supports have sizes 16, 16, and 20, and every
nonzero coefficient has both shared and divergent outcomes in
\(\{0,2\}\). Thus the deficiency is exact, rather than an inference from
modular rank. By the quotient-coordinate argument above, the 63 new
source images have rank 60 at this specialization. This is an external
exact-arithmetic result, **not a Lean certificate**; it does not yet
provide expanded nullvectors among all 162 original source columns.
See `exploration/conic_residue_nullspace.py` and
`exploration/conic-nullspace-results.json`. The perturbed economic
witnesses and their separate finite certificate status are recorded in
the exploration results.

## Coalescing time factors: exact column identities

This section records algebraic identities, not an all-length independence
proof. Keep one outcome pair \((a,b)\) fixed, use row vectors, and write

\[
 K_i(\varepsilon)=K+\varepsilon D_i+\varepsilon^2E_i+O(\varepsilon^3),
 \qquad p=X_aK(a,b),\qquad \ell(H)=X_aH(a,b).
\]

For common \(G\), independent linear time tilts
\(A_i=G\operatorname{diag}(1,1+\varepsilon\delta_i,
1+\varepsilon\zeta_i)\) give
\(D_i=\delta_iK_u+\zeta_iK_v\). The normalization of each transition
row generally makes \(E_i\ne0\); none of the identities below discards
these terms. Set \([H,J]=HJ-JH\).

For adjacent IDs \(u<v\) in the ordered set \(B\setminus\{t\}\), let
\(A\) be the ordered product before \(u\), and \(C\) the ordered
product after \(v\). The exact source-column difference is

\[
 \Delta_t(u,v):=F_{t,u,a,b}-F_{t,v,a,b}
 =X_aK_t(a,b)e_b(K_vAK_u-K_uAK_v)C.
\]

Replacing, for each fixed \(t,a,b\), its list of columns by one base
column and adjacent differences is an invertible constant column
operation. If \(u\) has position \(j\), counted from one in
\(B\setminus\{t\}\), and \(c\) IDs follow \(v\), the first
coefficient of this difference is

\[
 [\varepsilon]\Delta_t(u,v)
 =p\,e_b[D_v-D_u,K^j]K^c.
\]

The first derivatives of the common prefix, suffix, and scalar prefactor
cancel. These repeated first coefficients permit further constant column
operations with genuinely second-order leading terms.

For three consecutive global IDs \(r<s<t\), put
\(U=D_s-D_r\), \(V=D_t-D_r\), let \(j-1\) be the number of IDs
before \(r\), and let \(c\) be the number after \(t\). The triangle
combination

\[
 H=\Delta_t(r,s)+\Delta_r(s,t)-\Delta_s(r,t)
\]

has zero coefficients of orders zero and one, and

\[
 [\varepsilon^2]H
 =e_b\left\{
   \ell(V)[U,K^j]-\ell(U)[V,K^j]
   +p\bigl(VK^{j-1}U-UK^{j-1}V\bigr)
 \right\}K^c. \tag{C1}
\]

Here is a direct derivation that also checks the cancellation of every
\(E_i\). Let \(A\) and \(C\) be the common actual prefix and suffix,
\(U_*=K_s-K_r\), \(V_*=K_t-K_r\), and \(p_r=X_aK_r(a,b)\).
Expansion of the three column differences gives the exact identity

\[
 H=e_b\{\ell(V_*)(U_*AK_r-K_rAU_*)
       -\ell(U_*)(V_*AK_r-K_rAV_*)
       +p_r(V_*AU_*-U_*AV_*)\}C.
\]

Every term has two matrix differences. Taking their first coefficients
and the zeroth coefficients of the remaining factors proves (C1).
For two time directions, (C1) is their alternating bilinear form
multiplied by the signed area of the three time-tilt vectors.

There are also second-order identities from moving the shared slot.
Fix a globally adjacent edge \(u<v\), with \(L\) IDs before \(u\)
and \(R\) after \(v\). Set \(V=D_v-D_u\).
If adjacent shared IDs \(t,t'\) occupy zero-based prefix positions
\(k,k+1\), where \(0\le k\le L-2\), put \(U=D_{t'}-D_t\).
The coefficients of orders zero and one in
\(\Delta_t(u,v)-\Delta_{t'}(u,v)\) vanish, and the second is

\[
 e_b\left\{-\ell(U)[V,K^L]
   +p\left(VK^kUK^{L-k-1}
          -K^{k+1}UK^{L-k-2}V\right)\right\}K^R. \tag{C2}
\]

For adjacent shared IDs in suffix positions \(k,k+1\), with
\(0\le k\le R-2\), the corresponding second coefficient is

\[
 e_b[V,K^{L+1}]
   \left\{pK^kUK^{R-k-2}-\ell(U)K^{R-1}\right\}. \tag{C3}
\]

To derive (C2), the difference of the first prefix derivatives is
\(K^kUK^{L-k-2}\), whereas the difference of the scalar derivatives
is \(-\ell(U)\). Substitution in the adjacent-edge identity gives
the displayed expression. The same argument on the suffix proves (C3).
All common second derivatives cancel. With three consecutive shared
prefix slots having equal increments \(U\), a second finite difference
also cancels the scalar term in (C2), giving

\[
 p e_b\left\{VK^k[U,K]K^{L-k-2}
       -K^{k+1}[U,K]K^{L-k-3}V\right\}K^R,
 \qquad 0\le k\le L-3. \tag{C4}
\]

These are constant combinations of the original source columns. No
effect-dependent coefficients have been used to change the column span.

The second-order alternating form does not vanish identically for
softmax transitions. At the boundary matrix

\[
 G=\begin{pmatrix}1&1&1\\1&1&0\\1&0&1\end{pmatrix},
 \qquad X=(1,1,1),\quad u=v=1,
\]

take \(U=K_u\), \(V=K_v\), \(a=b=0\), and \(j=1\). Then

\[
 e_0\{V_{00}[U,K]-U_{00}[V,K]+K_{00}(VU-UV)\}
       =(0,-1/54,1/54),\qquad \det K=-1/12.
\]

Thus no suffix power kills this particular row. Although this boundary
matrix has zero entries and fails some residue-geometry assumptions, the
displayed rational coefficient is defined and nonzero. Continuity gives
strictly positive nearby common matrices with the same nonvanishing
property. This establishes a nonzero second-order column for arbitrary
suffix length, not independence from other columns.

The same boundary matrix supports two independent spectral variables.
On the zero-sum row space, let \(\tau=\operatorname{tr}K-1\) and
\(d=\det K\). For \(X=(1,t,s)\), put
\(A=1+t+s\), \(B=1+t\), \(C=1+s\). Direct computation gives

\[
 \tau=1+A^{-1}-B^{-1}-C^{-1},\qquad
 d=-\frac{ts}{ABC}.
\]

At \((t,s)=(1,2)\), their derivative rows are
\((3/16,7/144)\) and \((-1/48,1/144)\), so the Jacobian is
\(1/432\). Their image therefore contains an open set, proving that
\(\tau\) and \(d\) are algebraically independent. The nonzero
Jacobian also persists under a small positive perturbation of \(G\).

After spectral decomposition, (C2)--(C4) contain terms with two varying
nonstationary eigenvalue exponents. This is a possible source of the
quadratic number of independent directions needed as \(n\) grows.
However, the accompanying coefficients also depend on the effects, and
the remaining terms have not been eliminated. Algebraic independence of
the spectral invariants does not by itself establish independence of these
columns. A nonsingular full leading matrix, or an equivalent Laurent
determinant argument, remains unproved. Independence of stacked Taylor
coefficients is not a substitute: pointwise column relations may have
\(\varepsilon\)-dependent coefficients.

As a check on the identities, `exploration/coalescent_checks.py` verifies
the adjacent-edge coefficient and (C1)--(C3) directly from exact rational
series of the original \(F\) columns, retaining normalization terms.
The recorded cases cover \(n=3,\ldots,6\), two positive common matrices,
three effect vectors, and every outcome pair: 2,160 adjacent-edge checks
and 540 checks for each of the triangle, prefix, and suffix formulas.
It also checks the boundary curvature and spectral Jacobian. These are
external spot checks of the algebraic identities, not rank certificates
or Lean proofs; (C4) follows by subtraction of (C2).

## A last-block degeneration and its binary obstruction

The inverse-matrix filtration above permits a more explicit boundary
calculation, but its simplest candidate polar block is singular. Normalize
the first column of the common matrix \(G\) to one, put
\(\alpha_a=G_{a1}\), \(\beta_a=G_{a2}\), and choose the last block
as \(A_N=G\operatorname{diag}(1,\varepsilon,\varepsilon^B)\), with
integer \(B>1\). On its line \(L_{Na}=0\), use the affine parameter

\[
 X_1=1,\qquad X_2=z,\qquad
 X_0=-\varepsilon\alpha_a-\varepsilon^B\beta_a z.
\]

For invertible \(G\) and nonzero \(\alpha_a z\), the exact inverse
formula gives

\[
 \varepsilon^{B-1}K_N^{-1}
 \longrightarrow z^{-1}E_{22}G^{-1}
       \operatorname{diag}(\alpha_c-\alpha_a)_{c=0}^2. \tag{L1}
\]

Only row two can survive. Its row sum is zero, because row two of
\(G^{-1}\) annihilates both the first and second columns of \(G\).
Its component \(a\) is also zero. Under generic conditions this row is
nonzero, as expected for the one-dimensional new-line residue direction.

Divide each shared-\(N\) source column by the nonzero constant
\(A_N(a,b)\), multiply it on the right by \(K_N^{-1}\), and take
its residue along \(L_{Na}=0\). The resulting row is exactly

\[
 X_aX_b\,e_b(I-P_s^{\mathrm{old}})K_N^{-1}.
\]

Write \(\kappa_i=1\) for \(i=0\) and zero otherwise. After multiplying
this column by the constant power
\(\varepsilon^{B-1-\kappa_a-\kappa_b}\), its limit is the common row in
(L1) times
\(X_a^0X_b^0[e_b(I-P_s^{\mathrm{old},0})]_2\), where
\((X_0^0,X_1^0,X_2^0)=(-\alpha_a,1,z)\).
The limiting old transitions have zero first column; after one step a
path stays in the binary state set \(\{1,2\}\).

The \(b=0\) column for a given \(s\) has a row-zero pole only at
\(L_{s0}|_{X_0=0}=0\). Later matrices use only rows one and two.
For distinct restricted lines and invertible binary transitions, these
\(m\) poles form a diagonal nonzero block. The other \(2m\) columns
are, up to a shared nonzero rational factor and signs,

\[
 q(P_s)(z),\qquad z\,r(P_s)(z),
\]

where \(q(P)=P_{12}\), \(r(P)=P_{21}\), and \(P_s\) orders
the \(m\) old binary transitions with \(s\) first. Their generic
independence would have made this particular polar half sufficient.
It is false already for \(m=2\).

The failure has a short exact calculation. Common \(G\) makes the two
binary row odds \(c_i z\) and \(\rho c_i z\), with common
\(\rho\ne1\). If \(d_i\) is the binary determinant, set

\[
 H_i=d_i^{-1}
  =\frac{(1+c_i z)(1+\rho c_i z)}{(\rho-1)c_i z},\qquad
 Q_i=\frac{q_i}{d_i}=\frac{1+\rho c_i z}{\rho-1},\qquad
 R_i=\frac{zr_i}{d_i}=\frac{1+c_i z}{(\rho-1)c_i}.
\]

Dividing every column by the common rational function
\(\prod_i d_i\) is an injective linear transformation. In any word
order, its two columns become the sums of \(Q_i\), respectively
\(R_i\), times the preceding \(H\) products. These are Laurent
polynomials supported on powers \(1-m,\ldots,m\).
Moving slot \(s\) to the front changes the first sum by

\[
 h_s=\sum_{i<s}\frac{c_i-c_s}{c_ic_s(\rho-1)^2}
       \bigl(z^{-1}+\rho(c_i+c_s)+\rho c_ic_sz\bigr)
       \prod_{j<i}H_j,
\]

and changes the second by \(-z h_s\). The formula follows from
\(H_i-1=Q_i+R_i/z\). The pairs \(h_s,z h_s\), for
\(s=2,\ldots,m\), are independent when consecutive \(c_i\)'s
are distinct: their successive outer powers are unique. They leave a
two-dimensional Laurent remainder, which need not be filled by the two
ascending baseline columns.

Indeed, for \(m=2\), let
\(J=1+\rho(c_1+c_2)z+\rho c_1c_2z^2\). Direct factorization gives

\[
 h_2=\frac{(c_1-c_2)J}{c_1c_2(\rho-1)^2z},\quad
 Q_{\mathrm{base}}=\frac{(1+\rho c_1z)J}{(\rho-1)^2c_1z},\quad
 R_{\mathrm{base}}=\frac{(1+c_1z)J}{(\rho-1)^2c_1c_2z}.
\]

Both baseline columns lie in the span of \(h_2,z h_2\). The four
binary columns therefore have rank exactly two for
\(c_1\ne c_2\) and \(\rho\ne1\). Consequently the leading
shared-\(N\) polar half above is deficient when \(m=2\). This
rules out that particular simple leading block, not the complete
Schur complement: the other new columns and higher powers of
\(\varepsilon\) have not been eliminated or shown dependent.

In fact the binary rank has an exact parity law for every length:

\[
 \operatorname{rank}\{q(P_s),zr(P_s):1\le s\le m\}
 =\begin{cases}2m,&m\text{ odd},\\2m-2,&m\text{ even}.
 \end{cases} \tag{L2}
\]

Assume \(\rho\ne0,1\), all \(c_i\ne0\), and consecutive
\(c_i\)'s distinct. The rank means linear independence over constant
real coefficients, for rational functions of \(z\); it is not rank
over \(\mathbb R(z)\). Lean now proves the scalar-span parity
recurrence, both baseline remainders, Laurent endpoint independence,
and the rank theorem for the actual nonempty moved-word family of
normalized \(Q/R\) prefix sums under the displayed assumptions.
Identifying those sums with the matrix-product columns \(q(P_s),zr(P_s)\)
after division by the common determinant product remains a paper
argument, as does the later polar perturbation.

Let \(Q^{(k)},R^{(k)}\) be the ascending prefix sums for the first
\(k\) blocks, with empty sums zero, and write

\[
 A^{(k)}=\prod_{i\le k}H_i=1+Q^{(k)}+R^{(k)}/z.
\]

For an appended odds parameter \(c\), write
\(h_{k+1}(c)=(R_cQ^{(k)}-Q_cR^{(k)})/z\), and set \(h_1=0\).
Define the scalar Laurent polynomial

\[
 \Phi_k(c)=-\frac{1+\rho cz}{z}R^{(k)},\qquad \Phi_0=0.
\]

With \(e=c_k\), direct substitution gives the exact recurrence

\[
 \Phi_k(c)=1-\Phi_{k-1}(e)
       +\frac{\rho-1}{e-c}
          \bigl(eh_k-ch_{k+1}(c)\bigr). \tag{L3}
\]

To check it, substitute
\(Q^{(k)}=U+A^{(k-1)}Q_e\),
\(R^{(k)}=V+A^{(k-1)}R_e\), where
\(A^{(k-1)}=1+U+V/z\). The only two-block identity needed is

\[
 (1+cz)Q_e-e(1+\rho cz)R_e=(e-c)z.
\]

After multiplying (L3) by \((e-c)z\), the remaining expression is
\((e-c)z(A^{(k-1)}-1-U-V/z)=0\).
Induction in (L3) proves that \(\Phi_k(c)\), modulo the scalar
span of \(h_2,\ldots,h_{k+1}(c)\), is one for odd \(k\) and
zero for even \(k\).

It remains to connect this scalar recurrence to the two baseline
columns. For \(m\ge2\), put \(c=c_{m-1}\), \(d=c_m\),
\(U=Q^{(m-2)}\), \(V=R^{(m-2)}\), and

\[
 v_Q=\frac{d(1+\rho cz)}{c-d},\qquad
 v_R=\frac{1+cz}{c-d}.
\]

The exact outer-column elimination is

\[
 Q^{(m)}-v_Qh_m=Q_d S,\qquad
 R^{(m)}-v_Rh_m=R_d S, \tag{L4}
\]

where

\[
 S=\frac{d(1+\rho cz)V-(1+cz)U}{(c-d)z}
   =\Phi_{m-2}(c)-\frac{c(\rho-1)}{c-d}h_{m-1}.
\]

Although \(v_Q,v_R\) are linear polynomials in \(z\), (L4) uses
only constant multiples of the already available columns \(h_m,z h_m\).
For an explicit verification, put \(A=1+U+V/z\). Then
\(Q^{(m)}=U+A Q_{cd}\), \(R^{(m)}=V+A R_{cd}\), and
\(h_m=(R_dU-Q_dV)/z+A h_{cd}\). The two-block factorization gives
\(Q_{cd}=v_Qh_{cd}\), \(R_{cd}=v_Rh_{cd}\), while
\(R_dv_Q-Q_dv_R=z\). Subtraction proves (L4).

By (L3), \(S\) is congruent to the parity of \(m\) modulo the
scalar span of the earlier \(h\)'s. Multiplication by the linear
polynomials \(Q_d,R_d\) puts the discarded terms in the paired span
of \(h_s,z h_s\). Thus the two baseline remainders are exactly
\(Q_m,R_m\) for odd \(m\), and both zero for even \(m\).
The independent paired columns have no nonzero combination supported
only on \(1,z\), by the same outer-power elimination used above.
Finally, the coefficient determinant of \(Q_m,R_m\) in that central
basis is \(-1/(\rho-1)\ne0\). This proves (L2), including \(m=1\).

Under the separate generic assumptions making the row-zero pole block
nonzero and disjoint from the binary poles, the leading shared-\(N\)
polar half consequently has rank \(9m\) for odd \(m\), and
\(9m-6\) for even \(m\): there are three independent new-line
blocks, each consisting of \(m\) row-zero poles plus the binary rank
in (L2). These are ranks of this particular leading boundary block.
They are not ranks of the full Schur complement at general parameters.

The finite calculations in `exploration/binary_laurent.py` and
`exploration/binary-laurent-results.json` agree with (L2): ranks
\(2,2,6,6,10,10\) for \(m=1,\ldots,6\), using
\(\rho=2,-1\) and \(c_i=i\) or \(2^{i-1}\). The proof above
establishes the general parity law independently of those checks.

The exact binary kernel can also guide a correction away from the
boundary. At \(m=2\), write \(A_{12}=P_{12}(1,2)\) and
\(B_{12}=z(1-P_{12}(2,2))\), and similarly for the reverse word.
The two constant relations at \(X_0=0\) are

\[
 A_{12}-A_{21}-c_2B_{12}+c_1B_{21}=0,
\]
\[
 c_1A_{12}-c_2A_{21}
       -\rho c_1c_2B_{12}+\rho c_1c_2B_{21}=0.
\]

Differentiating these relations gives candidates for the two lost
directions on each new line. Choosing \(B\ge3\) controls the other
terms in this derivative: in (L1), the scaled inverse's row two is its
displayed limit plus \(O(\varepsilon^{B-1})\), and rows zero and one
are \(O(\varepsilon^{B-1})\). Also
\(X_0/\varepsilon=-\alpha_a+O(\varepsilon^{B-1})\). Thus the
inverse-matrix functional and the normalized coordinate prefactors have
zero first derivative. Only the old transition matrices vary at first
order, through \(X_0'=-\alpha_a\). A moving old cross-point adds
\(z'\partial_z\) of a zeroth-order nullrelation, which is zero because
that relation vanishes identically as a rational function.

More explicitly, at \(X_0=0\) write
\(k_i=(\eta,1,\rho)_i\), where
\(\eta=\beta_0\alpha_1/(\alpha_0\beta_1)\). Then

\[
 K_t^0(i)=\left(0,\frac1{1+k_ic_tz},
                       \frac{k_ic_tz}{1+k_ic_tz}\right),\qquad
 \left.\frac{\partial K_t(i)}{\partial X_0}\right|_0
 =\frac{e_0-K_t^0(i)}{\alpha_i u_t(1+k_ic_tz)}.
\]

Product differentiation therefore specifies the actual first kernel
derivatives. Their row-zero pole parts can be removed using the leading
row-zero columns. The even-length calculation below identifies a
nonzero coefficient for the two remaining directions. In particular,
the boundary obstruction does not imply singularity of the generic
shared-\(N\) polar half.

There is useful remaining parameter freedom. Keeping all \(c_t\) fixed
while varying \(u_t\), and choosing \(v_t\) accordingly, preserves
every leading transition matrix and the leading column kernel. Each
transition derivative has the scalar factor \(1/u_t\). Thus the first
kernel-derivative matrix after the fixed leading elimination is linear in
the independent parameters \(1/u_t\); its two-dimensional missing
determinant on each new line is quadratic in those parameters. A nonzero
coefficient suffices for this polar correction, but still leaves the
separate regular half of the full Schur complement.

## An explicit even-length polar first-order coefficient

This section proves an algebraic lemma over constant real column
coefficients and connects it to the full shared-\(N\) polar block.
The paper proof received an independent internal audit in
[SOURCE24_POLAR_AUDIT.md](../reviews/SOURCE24_POLAR_AUDIT.md).
It is not a proof of independence of the whole source family: the other
half of the Schur complement is still open. The polar argument has not
been formalized in Lean.

Let \(m\ge2\) be even, retain \(\rho\ne0,1\), and put
\(c=c_{m-1}\), \(d=c_m\), \(e=c_1\). Assume all
\(c_t\ne0\), adjacent \(c_t\)'s are distinct, and write

\[
 D=\prod_{t=1}^m d_t,\qquad
 I_m=\operatorname{span}_{\mathbb R}\{h_s,zh_s:2\le s\le m\},
 \qquad V_m=\operatorname{span}_{\mathbb R}\{z^{1-m},\ldots,z^m\}.
\]

The parity theorem says \(V_m=I_m\oplus\operatorname{span}\{1,z\}\).
Write \(\Pi:V_m\to\operatorname{span}\{1,z\}\) for this
constant-linear projection. For a move-first word \(P_s\), use scalar
columns \(A_s=q(P_s)\), \(B_s=zr(P_s)\); an overall minus
sign in the original first column is immaterial.

The row-zero columns must be included in the same scalar quotient.
If their row odds are \(\eta c_tz\), direct binary propagation gives

\[
 \frac{P_s(0,2)}D=Q_{\mathrm{word}\ s}+Z_s,\qquad
 Z_s=\frac{\eta-1}{\rho-1}\frac{1+\rho c_sz}{1+\eta c_sz}.
 \tag{P1}
\]

Here \(Q_{\mathrm{word}\ s}=A_s/D\). Since \(m\) is even,
each such Laurent column belongs to \(I_m\), so the full leading
scalar span is exactly
\(I_m+\operatorname{span}\{Z_1,\ldots,Z_m\}\).
Assume \(\eta\ne0,1,\rho\), and that the poles
\(-1/(\eta c_s)\) are distinct and disjoint from all binary poles
\(-1/c_t,-1/(\rho c_t)\). Each \(Z_s\) then has its own
nonzero pole and the sum is direct. This removal of the Laurent part
of a row-zero column uses constant combinations of the binary columns.

The two-dimensional binary column kernel can be parametrized by its
last-word coefficients \((p,q)\), those of \((A_m,B_m)\).
To see this, let \(S_A,S_B\) be the total coefficients of the two
column types in a relation. The outer \(h_m,zh_m\) terms in (L4)
give

\[
 p=-\frac{dS_A+S_B}{c-d},\qquad
 q=\frac{\rho cdS_A+cS_B}{c-d}.
 \tag{P2}
\]

Their determinant is \(cd(\rho-1)/(c-d)^2\ne0\). The earlier
paired \(h\) columns determine the other coefficients uniquely.
Thus choose a constant kernel basis with last coefficients
\((1,0)\), \((0,1)\). If \(C_A,C_B\) denote the sums over
the earlier words in any relation, its endpoints give

\[
 dC_A+C_B=-cp-q,\qquad
 C_A+\frac{C_B}{\rho d}=-p-\frac q{\rho c}.
 \tag{P3}
\]

Indeed the last block is \(m\) for every earlier word and \(m-1\)
for the last word; at zero the two columns have leading terms
\(c_{\mathrm{last}}z,z\), and at infinity they have limits
\(1,1/(\rho c_{\mathrm{last}})\).

Keep every \(c_t\) fixed and isolate the derivative coefficient
with only \(w_m=1/u_m\) nonzero. Normalize it to one. For now also
take the boundary \(1/\alpha_1=0\), \(1/\alpha_2=1\).
The attainable positive-parameter limit justifying this choice is
given below. The derivative of the last transition then has binary
row factors \(h_1=0\), \(h_2=r_d=1/(1+\rho dz)\).
All earlier words end with this transition. If their preceding binary
distribution is \(\pi\), the derivative of its final probability
of state two is \(w_1+(w_2-w_1)\pi_2\), where
\(w_i=-h_iB_m(i,2)\). Consequently

\[
 A_s'=\lambda A_s+k_A,\quad B_s'=\lambda B_s+k_B\quad(s<m),
\]
\[
 \lambda=-\frac{\rho(1+dz)}{(\rho-1)(1+\rho dz)},\qquad
 k_A=dk_B,\qquad k_B=\frac{\rho z}{(\rho-1)(1+\rho dz)}.
 \tag{P4}
\]

For the last word, let \(q_0=(K_1^0\cdots K_{m-1}^0)_{02}\).
The exceptional transition is first, so
\(A_m'=0\) and
\(B_m'=zr_d(1-q_0)-r_dB_m\).
Subtracting \(\lambda\) times the identically zero original kernel
relation, and applying (P3), gives its two derivative defects

\[
 N_p=\frac{\rho}{(\rho-1)(1+\rho dz)}
                \bigl((1+dz)A_m-cz\bigr),\qquad
 N_q=\frac{B_m-zr_d}{\rho-1}-zr_dq_0.
 \tag{P5}
\]

Using an effect-dependent multiplier on an identity that is already
zero here is only a way to compute its derivative; it is not an
effect-dependent change of source columns. The kernel basis and the
subsequent quotient operations all have constant coefficients.

Set \(U=Q^{(m-1)}\), \(V=R^{(m-1)}\). The product identities are

\[
 A_m/D=Q_d+H_dU,\quad B_m/D=R_d+H_dV,\quad
 q_0/D=H_d(U+Z_1),\quad D^{-1}=H_d(1+U+V/z).
\]

Substitution in (P5) gives the useful closed forms

\[
 \frac{N_p}D=\frac{\rho(1+dz)}{(\rho-1)^2dz}
       \bigl((1+(d-c)z)U-cV+(d-c)z\bigr),
 \tag{P6}
\]
\[
 \frac{N_q}D=\frac{\rho R_d}{\rho-1}(dV-U)-R_dZ_1.
 \tag{P7}
\]

All four shifted Laurent reductions needed for (P6)--(P7) follow
from the scalar recurrence, without treating a vector-space quotient
as a ring. Since the prefix length \(m-1\) is odd,
\(\Pi U=Q_c\), \(\Pi V=R_c\). Also
\(\Phi_{m-1}(d)=-V/z-\rho dV\) is one modulo the scalar span
of \(h_2,\ldots,h_m\). Applying this identity and its product by
\(z\), whose discarded terms are available \(zh_s\) columns,
gives the last two of

\[
 \begin{aligned}
 \Pi(U/z)&=-d-dQ_c,&\quad \Pi(zU)&=-z-Q_c/d,\\
 \Pi(V/z)&=-1-\rho dR_c,& \Pi(zV)&=-z/(\rho d)-R_c/(\rho d).
 \end{aligned} \tag{P8}
\]

The first two follow in the same way from the exact identity
\((\rho-1)dh_m=U/z+dU+d\Phi_{m-1}(d)\) and its product
by \(z\). Thus every removal in (P8) uses a constant combination
of the displayed paired columns.

Expanding (P6) and applying (P8) now yields

\[
 \Pi(N_p/D)=P(z)=\frac{\rho}{(\rho-1)^2}(1+cz).
 \tag{P9}
\]

The Laurent part of (P7) reduces to \(Q_c/((\rho-1)c)\).
To reduce the positive factor \(R_dZ_1\), remove its row-zero
pole by subtracting the constant \(R_d(z_0)\) times \(Z_1\),
with \(z_0=-1/(\eta e)\):

\[
 (R_d(z)-R_d(z_0))Z_1
   =\frac{\eta-1}{(\rho-1)^2\eta e}(1+\rho ez).
 \tag{P10}
\]

Retaining the minus sign of \(-R_dZ_1\) in (P7), the second
class modulo the entire leading scalar span is therefore

\[
 Q(z)=\frac1{(\rho-1)^2}
       \left(\frac1c-\frac{\eta-1}{\eta e}+\frac\rho\eta z\right).
 \tag{P11}
\]

The coefficient determinant of \(P,Q\) in the basis \(1,z\) is

\[
 \det(P,Q)=\frac{\rho}{\eta(\rho-1)^4}
       \left(\rho-\eta+\frac ce(\eta-1)\right).
 \tag{P12}
\]

It is nonzero for every even \(m\ge2\) at
\(\rho=2\), \(\eta=3\), \(c_t=5^{t-1}\): the bracket
is \(-1+2\cdot5^{m-2}>0\). Multipliers \(1,2,3\) times
different powers of five also give distinct binary and row-zero poles.

Here is how this coefficient is attained in the common-transition
parameter space. More generally take

\[
 G_M=\begin{pmatrix}1&1&1\\1&M&M/\eta\\1&b&\rho b/\eta\end{pmatrix},
 \qquad
 A_t\sim G_M\operatorname{diag}(w_t,1,\eta c_t),
 \tag{P13}
\]

where the table equivalence is multiplication by the nonzero scalar
\(1/u_t\), and \(w_t=1/u_t\). For positive \(w_t\) this is
exactly the original table with \(v_t/u_t=\eta c_t\).
Every leading transition is independent of \(M,w_t\), while its
row derivative has factor \(w_t/\alpha_i\). Set \(w_m=1\),
earlier \(w_t=0\), and let \(M\to+\infty\). The row-one
derivative vanishes and the row-two derivative has the common factor
\(1/b\). The row-zero transition derivative never enters a binary
kernel relation: before the last block the leading distribution is
binary, and in the last word its initial state is binary. Thus (P6)--(P12)
are precisely this limiting coefficient after division by \(1/b\).
Restoring it multiplies (P12) by \(1/b^2\).

For the new table choose \(A_N=G_M\operatorname{diag}(1,\varepsilon,
\varepsilon^B)\) with integer \(B\ge3\). On new line \(a\),
the derivative also has common factor \(-\alpha_a\). Before
taking the \(M\) limit, divide by this nonzero factor, normalize
the explicit coordinate factors, and identify the nonzero inverse row
functional from (L1) with a scalar. Explicitly its constant row vector
is
\(e_2G_M^{-1}\operatorname{diag}(\alpha_j-\alpha_a)\),
up to the common rational factor \(1/z\). If the \(\alpha_j\)
are distinct it is nonzero: the nonzero row \(e_2G_M^{-1}\) sums
to zero because the first column of \(G_M\) is all ones, and
therefore has at least two nonzero entries. Some component other than
\(a\) survives. The resulting scalar normalization is constant in
\(z\), apart from a common injective rational multiplication.
The scaled inverse functional and normalized coordinate factors have
zero first \(\varepsilon\) derivative for \(B\ge3\), as shown
above. This normalization is necessary when \(\alpha_1=M\) grows.

For the explicit choice \(\rho=2,\eta=3,b=3\),
\(\det G_M=M/3+1\ne0\), and all entries are positive for
finite positive \(M\). The nonzero limiting rational coefficient
therefore persists at sufficiently large finite \(M\), and then
at small positive earlier \(w_t\). This supplies positive finite
old time factors, with one common positive invertible \(G_M\).
The same coefficient, up to the described nonzero factors, works on
all three new lines simultaneously. For each finite choice, sufficiently
small positive \(\varepsilon\) realizes the nonzero leading minor.

For completeness, independence of the scalar rational functions detects
the required old-new pole residues. Before division by \(D\), the
leading functions \(q(P_s),zr(P_s),P_s(0,2)\) vanish at zero and
are bounded at infinity. Their allowed finite poles are precisely the
distinct old restricted lines. The two kernel derivatives in (P5)
have the same endpoint properties and only simple allowed poles.
For \(N_p\), \(A_m\) has no pole at the last row-two denominator;
for \(N_q\), use \(B_m-zr_d=d_m\,zr(P_{\mathrm{prefix}})\)
in (P5). These identities exclude an extra double pole at the last
transition. Equivalently, moving-pole differentiation of an identically
zero leading relation has double-pole coefficient equal to the pole
velocity times its zero residue. A function in this span with all finite
residues zero is pole-free and bounded at infinity, hence constant,
and its value at zero makes it zero. Thus the residue map is injective
on the leading pivots and these derivative columns. The inverse's common
\(1/z\) factor is nonzero at every allowed pole and only rescales
the corresponding residue rows. A moving old cross-point contributes
\(z'\partial_z\) of the leading nullrelation, which is identically
zero.

This proves the following conditional paper lemma. Under the displayed
pole assumptions, for even \(m\), if
\(\rho-\eta+(c/e)(\eta-1)\ne0\), the normalized last-block
perturbation has two independent first kernel derivatives on each new
line. Hence the \(3m\)-column block on that line has a nonzero
leading minor after constant kernel elimination. For odd \(m\), the
corresponding leading block already has rank \(3m\). The three
new-line blocks are separate, so together their shared-new polar half
has a nonzero \(9m\)-column minor at positive finite perturbations
of the common-\(G\) family (P13).

In particular, the explicit powers-of-five choice proves that the
shared-new polar determinant is not identically zero on the common-
\(G\), independent-time parameter space for every \(m\ge1\).
Additional generic line-incidence conditions used elsewhere can be
imposed by a small perturbation inside this nonzero-minor neighborhood
whenever their polynomial factors are not identically zero on that same
parameter space. The scalar-covariate substitution discussed earlier
then applies to the resulting nonzero polynomial in independent time
factors. These conclusions do not supply the unproved regular half of
the full Schur complement.

The separate finite check `exploration/binary_polar_derivative.py`, with
results in `exploration/binary-polar-derivative-results.json`, verifies
eight exact rational fixtures: \(m=2,4,6,8\), each with
\((\rho,\eta)=(2,3),(3,2)\). It solves the actual constant
Laurent column kernel with prescribed last-word coefficients, checks
the four reductions coefficientwise, compares (P6)--(P7) to actual
three-state product derivatives at three rational points, and checks
the row-zero subtraction and (P12). These finite diagnostics support
the all-length algebra above; they do not replace it or certify full
source independence.

## Additional finite degeneration diagnostics

The sparse and absorbing computations are recorded separately in the
exploration scripts and results. Normalized sparse evaluations did not
provide a full witness. In the absorbing chart, the subsequent
first-order experiment used the constant kernel \(N\) of the zeroth
evaluation matrix \(M_0\), and tested
\([M_{0,\mathrm{pivot}},M_1N]\), explicitly verifying
\(M_0N=0\). This is the relevant column elimination, rather than
stacking \(M_0\) and \(M_1\).

For the tested independent and economic time factors, \(n=2\) had
zeroth rank 16 and full first-order rank 24; \(n=3\) had zeroth rank
31 and first-order rank 51 out of 63. These finite evaluation results
are in `exploration/absorbing-firstjet-results.json`. The latter case
does not furnish the required first-order witness. The tests do not
establish a universal rank upper bound, rule out higher-order excursions,
or prove an all-length source determinant. The exact identities and the
binary parity proof above remain separate from these
finite diagnostics.

## Rank-one transition filtration: a local result and a leading obstruction

The following paper calculation concerns constant-coefficient independence
of rational functions, with Laurent column operations in a parameter
\(\delta\). It does not establish the remaining regular determinant.
Let
\[
 G_\delta=\mathbf1\mathbf1^\top+\delta I,\qquad
 Y_{ti}=B_{ti}X_i,\quad l_t=\sum_iY_{ti},\quad
 \pi_t=Y_t/l_t,\quad
 \Sigma_t=\operatorname{diag}(\pi_t)-\pi_t^\top\pi_t.
\]
Then \(K_t=\mathbf1\pi_t+\delta\Sigma_t+O(\delta^2)\).
Right multiplication by \(K_t\) sends a zero-sum row to a row
divisible by \(\delta\). In particular, the dependence of a
length-\(q\) product on its initial state starts at order
\(\delta^q\).

Number the blocks \(1,\ldots,n\), fix \(t<k<n\), and compare
the two words on the blocks other than \(t\) that move \(k\),
respectively \(k+1\), to the front. Denote their products by
\(P_k,P_{k+1}\). They have a common suffix of length
\(r=n-k-1\), so
\[
 \delta^{-r}(P_k-P_{k+1})=\mathbf1u_k+O(\delta),\qquad
 u_k=(\pi_{k+1}-\pi_k)\Sigma_{k+2}\cdots\Sigma_n.
 \tag{R1}
\]
Their differing prefixes have length \(k\ge2\). Thus both the
constant and first coefficients in (R1) are independent of the
initial row. Divide each source column by its nonzero parameter-only
factor \(A_t(a,b)\), take the indicated adjacent word difference,
and divide by \(\delta^r\). Its leading coefficient is
\(X_aX_bu_k/l_t\). Taking the difference of its \((a,b)\)
and \((b,a)\) columns and dividing once more by \(\delta\)
has leading coefficient
\[
 \frac{X_aX_b(Y_{tb}-Y_{ta})}{l_t^2}\,u_k,
 \qquad a<b. \tag{R2}
\]
The cancellation of the common first coefficient in (R1) is essential
here; arbitrary stacks of derivatives would not be a rank certificate.

For this one fixed \((t,k)\), the six symmetric leading columns
and the three columns (R2) are independent. To see this, put
\(y_i=B_{ti}X_i\). Modulo \(l_t=y_0+y_1+y_2\), the three
cubic numerators are nonzero constant multiples of
\(y_0y_1(y_1-y_0)\), \(y_0y_2(y_2-y_0)\), and
\(y_1y_2(y_2-y_1)\). After substituting
\(y_2=-y_0-y_1\), the latter two have distinct nonzero pure
cubic terms, while the first has none. Their classes are independent.
The remaining six quadratic monomials are independent as well.
The common row \(u_k\) does not invalidate this argument:
\(\Sigma_j\) is invertible on zero-sum rows whenever all
\(X_i,l_j\) are nonzero, and \(\pi_{k+1}-\pi_k\ne0\)
there when the two time vectors are nonproportional. If the total lines
are distinct, these conditions hold at a generic point of \(l_t=0\).
Consequently this nine-column subfamily admits a nonzero leading minor
after the specified constant-in-\(X\) Laurent elimination.

There are nevertheless additional leading relations across shared
times. Write \(J_0=I-\mathbf1\mathbf1^\top/3\). On zero-sum
rows,
\(\Sigma_j^{-1}=l_j\operatorname{diag}(1/Y_j)J_0\).
Applying the same injective right multiplication
\((\Sigma_1\cdots\Sigma_n)^{-1}\) to every leading row gives
\[
 u_k(\Sigma_1\cdots\Sigma_n)^{-1}
 =-l_{k+1}\!\prod_{j<k}l_j\,
 \left(B_{ki}/B_{k+1,i}\right)_{i=0}^2J_0
 \operatorname{diag}(1/Y_k)J_0\cdots
 \operatorname{diag}(1/Y_1)J_0. \tag{R3}
\]
For fixed \(k\), the \(6(k-1)\) symmetric leading columns
with \(t<k\) therefore share a row factor and have scalar
polynomial factors in
\[
 \sum_{t<k}h_t\operatorname{Sym}^2(X_0,X_1,X_2),
 \qquad h_t=\prod_{\substack{j<k\\j\ne t}}l_j.
\]
This space has dimension at most \(3k\). Indeed, putting
\(r=k-1\), the \(r-1\) identities
\(l_t h_t=l_rh_r\), multiplied by arbitrary linear forms,
give \(3(r-1)\) independent coefficient relations among the
\(6r\) generators. For every \(k\ge3\),
\(3k<6(k-1)\). Thus the local nine-column calculation cannot be
assembled into global independence by only eliminating the three
outcome skews in each block. Further parameter orders and the additional
cross-time kernel would have to be controlled. No such global rank
claim is made here.

### Subsequent intrinsic refinements

`SOURCE24_COMPLETION_QUOTIENT.md` realizes the remaining map in a quotient
by the actual completed source products, preserving their incidence data.
`SOURCE24_RESIDUE_DIFFERENCES.md` derives an inverse-free full vector-pair
difference operator, its invertible action on the 3m auxiliary seeds, and
the corresponding feedback-zero decomposition. The latter also exhibits
three exact rational-zero relations at deletion length k=3; these are
distinct from the nonzero single-pole quotient examples above. Neither
refinement proves the remaining all-length transversality statement.

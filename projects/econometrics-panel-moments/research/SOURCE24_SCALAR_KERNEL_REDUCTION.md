# Scalar-kernel reduction of actual source independence

**Status: independently audited algebraic reduction, conditional on the
scalar/auxiliary fullness theorem. The remaining determinant is open.**

This uses actual source coefficient combinations. It does not assume
invertibility of the old source matrix O or independence of the N generators.
The scalar/auxiliary theorem is proved separately in
[SOURCE24_JOINT_EXTENSION_PROOF.md](SOURCE24_JOINT_EXTENSION_PROOF.md).

## Ambient spaces and actual lists

Fix m>=4 and common-G parameters in the required generic open. Put
r=9 binom(m,2), d=r+3m and D=prod_(t,a) L_ta. The zero-sum rational
moment-row ambient W0 has dimension 2r+3m. Its scalar image under
h(R)=R2/X2 has dimension d; its kernel W01 has dimension r. These
ambient facts do not require source independence; see (B20)--(B23) of
[SOURCE24_BINARY_QUOTIENT.md](SOURCE24_BINARY_QUOTIENT.md).

The formal N list V_N contains:

- F_(t,s,a,b)−F_(t,r(t),a,b), s different from t and r(t):
  9m(m−2) columns;
- every long-empty row F_(t,a): 3m columns;
- F_(t,r(t),a,0): 3m columns.

Here r(t) is the smallest other block. Its length is
k=2r−3m. Let G_sel denote the remaining 6m selected columns
F_(t,r(t),a,b), b=1,2. The concatenation [V_N,G_sel] is obtained
by invertible constant column operations from all long-empty and
all first-level source rows. Replacing long-empty rows using
F_(t,a)=E_(t,a)+sum_b F_(t,r(t),a,b) gives the actual reduced
source list of single-block E and all first-level F rows. This is a
coefficient change, with no independence assertion.

## Eliminate the scalar map without a source inverse

Choose coordinates on h(W0), and set A=h V_N. The zero-prefix
scalar theorem and Z_m contained in N make A onto. Choose a
parameter-only right inverse H and a coefficient-kernel basis K_A:

\[
 AH=I_d,\qquad \operatorname{im}K_A=\ker A.
 \tag{SK1}
\]

K_A has k−d=r−6m columns. This is the dimension of the coefficient
kernel; it includes every possible source relation. The following
r columns are actual scalar-zero combinations:

\[
 \mathcal R=[V_NK_A,\ G_{\rm sel}-V_NHh(G_{\rm sel})].
 \tag{SK2}
\]

The coefficient transformation from [V_N,G_sel] to [V_NH,mathcal R]
is invertible, since [H,K_A] is a basis of the N coefficient space.
As h(V_NH)=I_d, it follows that

\[
 [V_N,G_{\rm sel}]\text{ is independent}
 \quad\Longleftrightarrow\quad
 \mathcal R\text{ is a basis of }W_{01}.
 \tag{SK3}
\]

Changing H changes its corrected selected columns by combinations
of V_N K_A; changing K_A changes a coefficient basis. Thus the rank
criterion is intrinsic to the actual source family.

## Clear the scalar-zero rows and eliminate one line

Coordinate divisibility and row sum zero give the unique representation

\[
 R=\frac{X_0X_1p}{D}(e_1-e_0),\qquad
 \mathcal P_m=\left\{\frac{D R_1}{X_0X_1}:R\in W_{01}\right\}.
 \tag{SK4}
\]

This defines the polynomial space intrinsically. Every p has degree
3m−1, and dim P_m=r. Equivalently it is the span of the polynomials
D ell_ij/(L_i L_j) supplied by the ambient basis (B20). Those ambient
basis vectors have not been assumed to be actual source combinations.
The intrinsic definition also avoids replacing coincident points at
G* by distinct reduced points.

For the auxiliary line ell_w: X0+w X2=0, the accepted auxiliary map
on a scalar-zero row is exactly restriction of this polynomial:

\[
 -\frac1w\left.\frac{D R_1}{X_1X_2}\right|_{\ell_w}
       =p|_{\ell_w}.
 \tag{SK5}
\]

The zero-prefix joint theorem supplies 3m independent restriction
pivots among V_N K_A. Indeed every scalar-zero Z combination has
an N coefficient preimage in ker A, even if that representation is
not unique. Perform an invertible coefficient change within K_A to
place such pivots first. Use them to eliminate the line restrictions
of every remaining column of mathcal R, including the selected
output-one/two columns.

Every remaining polynomial vanishes on ell_w and is therefore divisible
by its defining linear form. Define

\[
 \mathcal P'_m=\{p/\ell_w:p\in\mathcal P_m,\ p|_{\ell_w}=0\}.
 \tag{SK6}
\]

Restriction is onto the 3m-dimensional binary form space by the
actual auxiliary theorem. Multiplication by ell_w is injective, so

\[
 \dim\mathcal P'_m=r-3m.
 \tag{SK7}
\]

The unresolved source-independence criterion is consequently:

> The r−3m divided residual polynomials from these same actual
> coefficient combinations must form a basis of P'_m.

This is an (r−3m)-square determinant. The dimensions begin 42,75,117
at m=4,5,6. Its nonvanishing is invariant under the scalar right
inverse, coefficient-kernel basis and trace-pivot choices. It is
not established by the dimension count.

Under the stronger generic geometry with six distinct points per
block, P_m can also be identified with the degree-(3m−1) ideal of
all three matching points and three same-block line intersections
per block. The matching and same-block residue conditions impose
those vanishings, and the converse follows from the same residue
conditions. If ell_w avoids those points, P'_m is its degree-(3m−2)
part. This optional ideal description is not used at G*, where some
points coincide; (SK4)--(SK7) are the operative definitions.

## Exact relationship to equation (24)

The actual column operations and double-residue reduction in
[SOURCE24_INDUCTION.md](SOURCE24_INDUCTION.md) identify independence
of the reduced list with det O_m nonzero. Consequently, under the
scalar/auxiliary theorem, (SK7)'s residual determinant is equivalent
to that actual source criterion. O_m invertibility has not been
used to construct this reduction.

Uniform nonvanishing, together with the shorter-panel indicator-lift
induction and its required finite bases, would prove independence
of equation (24). The residual nonvanishing and corresponding Lean
proof remain unfinished.

## Obstructions to two tempting shortcuts

The zero-prefix list has at most
9m(m−2)+3(m−1)=2r−6m−3 coefficients. Once its scalar image has
dimension d,

\[
 \dim(\operatorname{span}Z_m\cap W_{01})\le r-9m-3.
 \tag{SK8}
\]

Likewise the N list implies

\[
 \dim(\operatorname{span}V_N\cap W_{01})\le r-6m.
 \tag{SK9}
\]

These are upper bounds, with no source independence assumed. The
missing selected output-one/two columns are indispensable for filling
W01; a construction confined to Z or N cannot do so.

Onto restriction on each generic single line also does not imply
onto restriction on a second line after imposing the first restriction.
A 3m-dimensional frame can restrict isomorphically to generic lines
while having zero coefficient kernel after the first restriction.
The new theorem supplies the first line only.

Finally, append does not provide polynomial multiplication closure.
At G*, for new time (epsilon,v) and old scalar-zero R,

\[
 h(RK_n)=-\frac{\varepsilon vX_1R_1}{L_{n0}L_{n1}}.
 \tag{SK10}
\]

One must subtract an actual scalar lift before obtaining another
scalar-zero row. Its cleared polynomial depends on that coupled
source correction. The next concrete target is a rank-preserving
transport for these corrected combinations, or direct nonvanishing
of the residual determinant in (SK7).

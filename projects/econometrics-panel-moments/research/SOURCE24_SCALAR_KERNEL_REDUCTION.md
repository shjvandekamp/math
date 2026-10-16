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

## An ambient append recurrence at the required degree

There is now a useful ambient recurrence for the divided residual space.
This paragraph uses generic reduced six-point geometry, with Z_[q]
the union of the three matching and three same-block points per block.
Put f_(n,a)=X_a prod_(b different from a) L_nb and D_t=prod_b L_tb.
A triple-block quintic interpolation certificate is sufficient to
separate every old point in degree 3q−4 for q>=3: choose a triple
containing the point's block, take its quintic separator, and multiply
by D_t for every block outside that triple. Cross-nonincidence keeps
its target value nonzero, and its degree is 5+3(q−3)=3q−4.

Apply the already proved Lean theorem
`BlockExtension.exists_corrected_cubic_decomposition` at k=3q−4.
Its input degree is k+5 and its coefficient degree is k+2. Therefore

\[
 I(Z_{[q+1]})_{3q+1}
   =\sum_{a=0}^2 f_{n,a} I(Z_{[q]})_{3q-2},\qquad q\ge3.
 \tag{SK11}
\]

The inclusion from right to left is immediate; the reverse inclusion
is the corrected cubic decomposition. Its other hypotheses are the
nonzero old point representatives, the new block's local line and
six-point conditions, and nonvanishing of each new line at each old
point. All are generic geometry conditions. No source rank is used.

The bounded verifier
[source24_triple_quintic.py](../exploration/source24_triple_quintic.py)
and its [exact certificate](../exploration/source24-triple-quintic-results.json)
record the required 18-by-18 minor, equal to 450004 modulo 1,000,003.
The fixture is G=((1,1,1),(1,30,10),(1,3,2)), with time factors
(8^t,8^(2t)), t=1,2,3. The full 18-by-21 quintic evaluation matrix,
point labels, monomials and geometry checks are saved. The run used
0.001083 seconds and 16,859,136 bytes RSS. The script and certificate
were independently reviewed without repeating the computation.
This is an external exact interpolation certificate, not a Lean proof
of the finite minor.

Its nonzero polynomial minor can be relabeled for each triple. For
every fixed finite q, multiply all required triple minors and geometric
nonvanishing conditions in the common-G parameter ring. The product
is nonzero and has positive real witnesses. This does not assert that
one prescribed geometric time sequence works at every length.
Together with the existing block-extension theorem, the certificate
proves (SK11) generically on paper.

The remaining source-realization issue is precise. For an old
scalar-zero and line-zero row
R=X0 X1 ell_w p/D_q (e1−e0), multiplication by X_a/L_na preserves
both vanishings and has new divided residual polynomial f_(n,a)p.
For an old long-empty difference
H_(s,b)=F_empty(1,b)−F_empty(s,b)=X_b e_b(P_s−P_1), actual outgoing
sources satisfy the exact identity

\[
 C_{n,s}^{ab}
   =-A_n(a,b)\frac{X_a}{L_{na}}H_{s,b}.
 \tag{SK12}
\]

This realizes cubic transport on those particular seeds. Multiplying
an old shared difference introduces an additional shared prefix and
is not automatically an available reduced source column. To use
(SK11) inductively, one must realize these three multipliers on the
actual residual coefficient kernel, retaining the same scalar and
line corrections. That closure is not proved here. Ambient ideal
generation and the seed identity alone do not imply it.

## The residual constraints leave the entire append prefix available

A further independently audited coefficient calculation identifies the
coupling that a transport proof must handle. Work with the full formal
list of local E_(t,a) and F_(t,s,a,b) columns at length q>=4. Write its
coefficients as lambda_(ta) and alpha_(tsab), and put

\[
 P_{tab}=X_aK_t(a,b)e_b,\qquad
 J_{tab}=\sum_{s\ne t}\alpha_{tsab},\qquad
 \mathcal I(c)=\sum_{t,a}\lambda_{ta}E_{ta}
                  +\sum_{t,a,b}J_{tab}P_{tab}.
 \tag{SK13}
\]

Appending the same coefficient vector to the actual new list gives

\[
 R_{\rm new}(c)=R_{\rm old}(c)K_n+
                  \mathcal I(c)(I-K_n).
 \tag{SK14}
\]

For F this is its exact ordered-word append identity; a local E remains
the same local E, which is also E K_n+E(I−K_n). Its prefix is E here,
not X_a e_a.

Since E_(ta)=X_a e_a−sum_b P_tab, the prefix rewrites as

\[
 \mathcal I(c)=\sum_a\Bigl(\sum_t\lambda_{ta}\Bigr)X_ae_a
             +\sum_{t,a,b}(J_{tab}-\lambda_{ta})P_{tab}.
 \tag{SK15}
\]

The 9q vectors P_tab are independent modulo the three diagonal
polynomials X_a e_a: at each distinct line L_ta, take the residue
component by component. Its numerator X_a A_t(a,b)X_b is not
identically zero on that line. Thus every coefficient of P_tab must
vanish; the three remaining diagonal polynomials are independent.
The prefix image has dimension 9q+3.

Its formal kernel is exactly J_tab=lambda_ta and sum_t lambda_ta=0.
A basis consists of the 9q(q−2) first-slot differences and the
3(q−1) long-empty differences. Hence this kernel is the formal
zero-prefix space Z, with dimension 9q²−15q−3.

Let K be the coefficient kernel of the full scalar-plus-auxiliary map.
Its dimension is r−3q. That joint map is onto already on Z, by the
new uniform theorem. For every coefficient vector c, choose z in Z
with the same joint observation. Then c−z belongs to K and has the
same prefix as c. Consequently

\[
 0\longrightarrow K\cap Z\longrightarrow K
    \xrightarrow{\mathcal I}\operatorname{im}\mathcal I
    \longrightarrow0,
 \qquad \dim(K\cap Z)=r-12q-3.
 \tag{SK16}
\]

These are dimensions of formal coefficient spaces, not claims about
independence of their actual rational-row images. They prove that
imposing the scalar and line constraints does not shrink the possible
prefix image. The correction in (SK14) cannot universally be discarded.

There is also a direct obstruction to averaging the arrival index.
Define beta(c) by the differences
alpha_(ts a1)−alpha_(ts a0) and alpha_(ts a2)−alpha_(ts a0), ignoring
E coefficients. Its formal kernel has dimension 3q². Therefore

\[
 \operatorname{rank}(\beta|_K)
       \ge (r-3q)-3q^2=\frac32q(q-5),\qquad q\ge6.
 \tag{SK17}
\]

The residual conditions do not force equal arrival-index coefficients.
Possible source relations are still included in K, so this does not
rule out balancing after adding other actual source corrections, nor
refute the desired multiplier closure. It identifies the nonzero
coefficient imbalance that such a construction must explicitly absorb.

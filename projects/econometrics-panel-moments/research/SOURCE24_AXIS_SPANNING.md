# The actual sources span every component-two axis observation

**Status: paper proof checked locally; not Lean formalized.** This result
uses actual first-slot differences and long-empty sources. It proves
surjectivity of the axis part T2 on N for every m>=3 under the positive
line-geometry hypotheses. It does not prove surjectivity of the full pair
and axis observation map C2, or equation-(24) independence.

The user-authorized [GPT-6 Pro investigation](https://chatgpt.com/c/6ad13994-ae68-83eb-a175-4d0f8aca9ffc)
supplied the argument. The primary researcher independently checked the
binary composition, the four source multipliers, the coprime-quadratic
step, both Laurent endpoints and the passage back to T2.

Use G=(1,alpha,beta), positive independent time factors u_t,v_t, and
the nondegeneracy assumptions in B25–B30 of `SOURCE24_BINARY_QUOTIENT.md`.
In particular all axis poles are distinct and nonzero. Put

\[
 x=X_1/X_2,\quad z_t=v_t/u_t,\quad
 \sigma=\beta_1/\alpha_1,\quad\tau=\beta_2/\alpha_2,\quad c=\tau-\sigma\ne0.
 \tag{AS1}
\]

On X0=0 the two-state kernel, its determinant and the total determinant are

\[
 B_t=\begin{pmatrix}x/(x+\sigma z_t)&\sigma z_t/(x+\sigma z_t)\\
 x/(x+\tau z_t)&\tau z_t/(x+\tau z_t)\end{pmatrix},\quad
 d_t=\frac{cz_tx}{(x+\sigma z_t)(x+\tau z_t)},\quad
 \Delta_m=\prod_td_t. \tag{AS2}
\]

Write L_[a,b]=span{x^a,...,x^b}. The rational functions with these 2m
simple poles, bounded at infinity and zero at x=0, form exactly
Delta_m L_[1−m,m]. Their residues determine them injectively: a bounded
pole-free difference is constant, and its value at zero fixes that constant.

## Exact source differences

For a binary stochastic product P let p(P)=P12 and d(P)=det(P). Then
p(PQ)=p(Q)+d(Q)p(P). In the increasing word omitting t, let Ppre be the
prefix preceding s and Ptail the suffix after s. Define

\[
 \kappa_s^{\widehat t}=
 \frac{(1-d_s)p(P_{\rm pre})-(1-d(P_{\rm pre}))p(B_s)}
 {d(P_{\rm pre})d_s}. \tag{AS3}
\]

The difference of the move-s-first and increasing products has the same
output-two entry in each row: their determinants agree. Binary composition
therefore gives the actual source identity

\[
 \left.\frac{(F_{t,s,a,b}-F_{t,r(t),a,b})_2}{X_2\Delta_m}
 \right|_{X_0=0}=-H_{t,ab}\kappa_s^{\widehat t}\quad(a,b\in\{1,2\}),
 \tag{AS4}
\]
\[
 H_{11}=\frac{x(x+\tau z_t)}{cz_t},\quad
 H_{12}=\frac{\sigma(x+\tau z_t)}c,\quad
 H_{21}=\frac{x+\sigma z_t}{cz_t},\quad
 H_{22}=\frac{\tau(x+\sigma z_t)}{cx}. \tag{AS5}
\]

These four multipliers span L_[−1,2] over parameter-only constants.
Indeed H12−sigma z_t H21=sigma z_t is a nonzero constant; H21 then
supplies x, H11 supplies x², and H22 supplies x^−1. Thus all four
Laurent multiples of every displayed kappa are actual source combinations.

## Six initial directions and two at each further block

When the prefix is the one block i and the moved block is j,

\[
 \kappa_{ij}=\frac{\sigma(z_i-z_j)}{c^2z_iz_j}\frac{Q_{ij}(x)}x,
 \qquad Q_{ij}=x^2+\tau(z_i+z_j)x+\sigma\tau z_iz_j. \tag{AS6}
\]

The actual pairs (t,s)=(3,2) and (2,3) supply kappa_12 and kappa_13
at every length m>=3. Later blocks are a common suffix, whose determinant
has already cancelled against Delta_m in AS4.

Q12 and Q13 are coprime: their difference is
tau(z2−z3)(x+sigma z1), while Q12(−sigma z1)=sigma(sigma−tau)z1²
is nonzero. Their products with degree-at-most-three polynomials span all
degree-at-most-five polynomials. To see the dimension exactly, a relation
A Q12+B Q13=0 with deg A,deg B<=3 forces A=Q13 C and B=−Q12 C,
where deg C<=1. The eight-dimensional coefficient domain has a
two-dimensional kernel and six-dimensional target. Multiplying by x^−2
gives

\[
 \kappa_{12}L_{[-1,2]}+\kappa_{13}L_{[-1,2]}=L_{[-2,3]}. \tag{AS7}
\]

For j=3,...,m−1 use the actual pair (t,s)=(m,j). Its prefix is
B1...B_(j−1); call AS3's value kappa_j. Each entry of B_t^−1 is
Laurent with exponents between −1 and 1, and
p(Ppre)/d(Ppre)=−(Ppre^−1)12. Consequently kappa_j is Laurent.
Its numerator in AS3 has expansions

\[
 \frac{z_{j-1}-z_j}{\tau z_jz_{j-1}}x+O(x^2)\quad(x\to0),\qquad
 \frac{\sigma(z_{j-1}-z_j)}x+O(x^{-2})\quad(x\to\infty). \tag{AS8}
\]

For the first expansion, a prefix of length at least two has
p(Ppre)=1−x/(tau z_(j−1))+O(x²); for the second its last block gives
p(Ppre)=sigma z_(j−1)/x+O(x^−2). The denominator has orders x^j
at zero and x^−j at infinity. Thus kappa_j has exact nonzero lowest
and highest powers 1−j and j−1.

Given L_[1−j,j], the two available functions x^−1 kappa_j and
x² kappa_j add its missing extremes −j and j+1, respectively. Starting
from AS7 and continuing to j=m−1 proves

\[
 \left\{\left.R_2/X_2\right|_{X_0=0}:R\in N\right\}
       =\Delta_m L_{[1-m,m]}. \tag{AS9}
\]

Every generator used here is an actual first-slot difference. In particular
the further extreme directions use the boundary index t=m.

## Completing all axis observations

For c=1,2 the T_(u,c),2 observations are nonzero rescalings of the
2m residues of AS9. They are therefore all spanned. The remaining m
coordinates can be adjusted independently using the actual long-empty
rows F_t0. The already proved B27 gives

\[
 T_{(u,c),2}(F_{t0})=0\quad((u,c)\ne(t,0)),\qquad
 T_{(t,0),2}(F_{t0})=-\prod_{j\ne t}d_j(Q_{t0,0})\ne0. \tag{AS10}
\]

Hence

\[
 T_2(N)=\mathbb K^{3m}\quad(m\ge3). \tag{AS11}
\]

No old-source inverse is used. For even m, the two left-kernel directions
of the long-empty axis block are therefore removed by first-slot
differences: B37 has rank two under these hypotheses at every even length.
This removes pure-axis annihilators uniformly. Annihilators with nonzero
pair weights remain the unresolved part of C2(N) spanning.

The proof constructs a parameter-rational right inverse: choose actual
source combinations N_i in N with T2(N_i)=e_i, and collect them as Nbar.
Laurent coefficient elimination, residue interpolation and AS10 use only
parameter-dependent scalar coefficients. Define

\[
 \widehat\rho_2(R)=\rho_2(R)-\rho_2(\overline N)T_2(R). \tag{AS12}
\]

Then rhohat2(Nbar)=0 and, for either parity,

\[
 \operatorname{rank}\mathscr C_2(N)
 =3m+\operatorname{rank}\widehat\rho_2(N). \tag{AS13}
\]

Indeed subtract Nbar T2(R) from every N generator to obtain the kernel
of T2 on N, while Nbar supplies its complementary 3m independent axis
coordinates. An annihilator a^T rho2+beta^T T2 must have
beta^T=−a^T rho2(Nbar). Thus the remaining target is a full-row-rank
r-dimensional pair observation map. This is an exact reduction; it does
not assert that remaining rank.

## Independent exact checks of the source formulas

`exploration/source24_binary_axis_spanning.py` builds pole residues from
the actual ordered binary kernels, separately from AS3–AS5. At m=3,...,8
the selected 4(m−1) columns have ranks 6,8,10,12,14,16, with nonzero
minor determinants 516277,126198,804552,196648,180041,76384 modulo
1,000,003. It checks AS4 at three ordinary points for every selected
column, reconstructs those values independently from their pole residues,
and verifies polynomial Bezout identities for Q12,Q13. All 324 formula
and 324 reconstruction checks pass. The primary researcher reviewed
the implementation.

The run took 0.0814 seconds with 15,433,728 bytes maximum RSS. Exact
parameters, labels and minors are in
`exploration/source24-binary-axis-spanning-results.json`. These checks
corroborate the formulas; AS7–AS11 provide the uniform proof.

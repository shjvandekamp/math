# Generic moment dimensions in three-choice dynamic logit with a scalar covariate

Mathematical manuscript, 15 October 2026. Both the arbitrary-period dimension
theorem and the four-period source-basis theorem compile end to end in Lean.
Their axiom audits and independent compiled-statement audits report **PASS**.
See VERIFICATION.md for clean source rebuild evidence and exact pinned versions.
The structural contribution is the cubic-product description of the likelihood
span and its induction over panel length. Novelty and priority remain
provisional; see NOVELTY.md. Independence of the proposed source family for
arbitrary panel length remains a separate question.

## The statistical question

Condition on initial state, covariates and common parameters. Individual
preferences enter choice probabilities through positive multipliers eta_q,
with eta_1=1. Positive index tables pi_t(q,r) give transition probabilities
pi_t(q,r)eta_q / sum_s pi_t(s,r)eta_s. Their products define path probabilities
p_y. The moment space consists of real path functions m such that
sum_y m(y)p_y(eta)=0 for every positive eta.

These restrictions eliminate unrestricted individual effects without specifying
their distribution. Counting all such moments determines whether a proposed
GMM family exhausts the available fixed-effect-free restrictions. Dimension
alone does not establish identification of the common parameters or efficiency
of a particular estimator.

The source [Dano, Honoré and Weidner (2026)](https://arxiv.org/html/2610.17104v1)
constructs an explicit family using permuted generation orders, conjectures
that it is a basis, and gives numerical evidence. We retain its model and
normalizations. The contribution here is a geometric description
of the entire likelihood span when there are three alternatives.

## From probabilities to cubic products

Temporarily homogenize the three effect coordinates, and write S=R[eta_1,eta_2,eta_3].
Let L_tr=sum_q pi_t(q,r)eta_q. After multiplying by

\[
 D=L_{1,y_0}\prod_{t=2}^T\prod_{r=1}^3L_{tr},
\]

the path likelihood becomes the homogeneous polynomial

\[
 F_y=A_y\prod_{t=1}^T\eta_{y_t}
       \prod_{t=2}^T\prod_{r\ne y_{t-1}}L_{tr},\qquad
 A_y=\prod_{t=1}^T\pi_t(y_t,y_{t-1})>0.
\]

Its degree is 3T−2. Positivity of D makes the moment identity equivalent to
the polynomial identity sum_y m_y F_y=0 after eta_1=1. A polynomial vanishing
on the positive orthant is zero; dehomogenization is injective on this fixed
homogeneous degree. Thus the restriction rank is the dimension of span{F_y}.

For t>=2 define h_tr=eta_r product_(s≠r)L_ts and H_t=span{h_t1,h_t2,h_t3}.
The path scalars A_y do not change the span, and the path indices vary
independently. Therefore, with m=T−1,

\[
 V_m:=\operatorname{span}\{F_y\}=S_1H_2\cdots H_T.
\]

## Six base points and interpolation

For the structural block formulas, use the Lean coordinate labels
X_0=eta_1, X_1=eta_2, X_2=eta_3. Divide each denominator by its positive
X_0 coefficient; this only rescales the cubic generators by nonzero constants
and preserves their span. Write the normalized block as

\[
 L_i=X_0+a_iX_1+b_iX_2,\qquad \ell_i=(1,a_i,b_i),\qquad i=0,1,2.
\]

Let lambda(v)=v_0X_0+v_1X_1+v_2X_2, and let e_i be the i-th coordinate
vector. Use the actual cross-product representatives

\[
 P_{ij}=\ell_i\times\ell_j,\qquad R_i=\ell_i\times e_i,
 \qquad z=(P_{01},P_{02},P_{12},R_0,R_1,R_2).
\]

The six explicit quadratic polynomials, in the same order, are

\[
 Q=\bigl(L_2\lambda(R_0\times R_1),\,
 L_1\lambda(R_0\times R_2),\,
 L_0\lambda(R_1\times R_2),\,
 L_1L_2,\,L_0L_2,\,L_0L_1\bigr).
\]

The general block hypotheses are exactly the following primitive conditions:

- For every i, a_i is nonzero or b_i is nonzero; for i≠j,
  a_i≠a_j or b_i≠b_j. These are `CubicRelations.LineConditions`:
  no normalized line equals X_0, and the lines are pairwise distinct.
  Over the reals the tests can equivalently be written
  a_i²+b_i²≠0 and (a_i−a_j)²+(b_i−b_j)²≠0.
- For each of the six indices j, Q_j(z_j)≠0. These are precisely
  `GeneralGeometry.LocalNondegenerate`.
- For distinct blocks u and v, every index j and every line index r,
  L_vr(z_uj)≠0. This is `GeneralGeometry.CrossNonincident`.

Each Q_j has degree two directly from its displayed product of two linear
forms. Cross-product orthogonality gives Q_j(z_i)=0 whenever i≠j, without
an additional geometric hypothesis. The six required diagonal values make
this evaluation matrix invertible. They also imply that every representative
z_i is nonzero and that the six projective points are distinct. No assumption
that all coordinates of a representative are nonzero is imposed.

For m>=1 blocks, multiply a local quadratic separator by every L_sr from the
other blocks. The resulting degree-3m−1 polynomial is zero at every other
point and nonzero at its own point. Hence evaluation on the 6m points is
surjective in degree 3m−1 and every higher degree. To pad degrees, multiply
each separator by a power of one coordinate nonzero at its target, then
rescale its target value to one. In particular,

\[
 \dim I(Z_m)_{3m+1}=\binom{3m+3}{2}-6m.
\]

## One block: all relations are explicit

With h_i=X_i product_(j≠i)L_j, let J=(h_0,h_1,h_2). The following
degree-two coefficient vectors are syzygies:

\[
 s_{01}=(-X_1L_0,X_0L_1,0),\quad
 s_{02}=(-X_2L_0,0,X_0L_2),\quad
 s_{12}=(0,-X_2L_1,X_1L_2).
\]

To describe the entire relation kernel, reduce any relation
sum_i c_i h_i=0 modulo L_i. The stated line conditions make L_i prime
and prevent it from dividing X_i or another L_j, so L_i divides c_i.
Writing c_i=L_i g_i and cancelling the nonzero product of the L_i gives
the exact equivalence with sum_i X_i g_i=0. Homogeneous projection
preserves the quotient degrees. This kernel equivalence supplies the
dimension calculation.

Put n=k−4>=0. Multiplication of the three coefficients by their respective L_i
identifies the kernel of S_(n+1)^3 -> J_(n+4) with the kernel of

\[
 S_n^3\longrightarrow S_{n+1},\qquad(g_0,g_1,g_2)\longmapsto\sum_iX_i g_i.
\]

This coordinate map is onto: every monomial of positive degree is divisible
by a coordinate, and homogeneous projection preserves the required degrees.
Rank-nullity consequently gives

\[
 \dim J_k=4\dim S_{k-3}-3\dim S_{k-4}
         =\dim S_k-6\quad(k\ge4).
\]

No negative-degree spaces or full free-resolution dimension theorem are needed.
Quadratic separators give the same
dimension for I(Z_1)_k. Since J_k is contained in this vanishing space,
J_k=I(Z_1)_k for every k>=4. This argument uses finite-dimensional
polynomial spaces; no saturation or sheaf-cohomology assertion is needed.

## Adding a block

Assume V_m=I(Z_m)_d, where d=3m+1. The case m=1 follows from the preceding
degree-four result, and V_0=S_1. Add a new six-point block Z'. For
F in I(Z_m union Z')_(d+3), single-block equality gives

\[
 F=h'_0c_0+h'_1c_1+h'_2c_2,\qquad c_i\in S_d.
\]

At each old point p, the vector c(p) lies in the kernel of the nonzero row
h'(p). All three new line values are nonzero by cross-block nonincidence,
and p is a nonzero vector by local nondegeneracy. Dividing the i-th
coefficient by L'_i(p) reduces the kernel equation to a coordinate
relation. Choosing any nonzero coordinate as a pivot proves that the
three evaluated vectors s'_01(p),s'_02(p),s'_12(p) span this kernel.
This allows any of the other coordinates of p to be zero. Choose three
scalar correction values at each p. Old-point interpolation supplies
polynomials B_01,B_02,B_12 of degree d−2=3m−1 with those values.

Replace c by c−sum_(i<j)B_ij s'_ij. The represented polynomial F is
unchanged, and each corrected c_i vanishes on every old point. By
induction each lies in V_m. Therefore

\[
 I(Z_m\cup Z')_{d+3}\subseteq V_m H',
\]

and the reverse inclusion is immediate from vanishing. For m=0 one uses
J'_4=I(Z')_4 directly, rather than negative-degree interpolation.
Induction proves V_m=I(Z_m)_(3m+1).

The resulting dimension formula is

\[
 \operatorname{rank}C=\binom{3T}{2}-6(T-1),\qquad
 \dim M=3^T-\binom{3T}{2}+6(T-1).
\]

This structural theorem for T>=1 under the stated primitive nonvanishing
conditions is proved by `CubicProducts.productSpan_eq_vanishingSpace` and
`StructuralMoments.finrank_moment_add_choose`. The conclusion concerns the
entire moment space's dimension,
without proving independence of the source's chosen list for general T.

## Economic attainability and density

The implemented scalar-covariate economic family has joint parameter domain
Theta_T=R^(T+6): four normalized state-dependence coefficients, two slopes,
and T covariates. The baseline outcome coefficient is one, so its block
denominators have exactly the normalized form above. Every a_ui and b_ui
is positive. In particular, the noncoordinate line condition holds
automatically.

The implemented economic exceptional product uses the following additional
sufficient condition: within each block, a_ur−a_us≠0 whenever r≠s. It is
stronger than merely requiring the coefficient pairs (a_ur,b_ur) and
(a_us,b_us) to differ. In the notation above, its exact factors are

\[
 \Delta_T(\theta)=
 \left(\prod_u\prod_{j=0}^5 Q_{uj}(z_{uj})\right)
 \left(\prod_u\prod_{v\ne u}\prod_{j=0}^5\prod_{r=0}^2 L_{vr}(z_{uj})\right)
 \left(\prod_u\prod_{r=0}^2\prod_{s\ne r}(a_{ur}-a_{us})\right).
\]

Here u and v range over the T−1 structural blocks, and all coefficients
and point representatives are the explicit functions of theta defined
above. `StructuralGenericity.genericRegion T` is exactly the set where
this fixed `exceptionalProduct` is nonzero. Its definition contains no
rank, span, or dimension condition. Together with positivity of the a_ui,
its factors imply all three general block hypotheses.

For z>1 set gamma_qr=(q−1)(r−1)log z, beta_q=q−1, x_t=3t log z. This
respects gamma_1r=gamma_q1=beta_1=0 and gives
L_tr=eta_1+w_tr eta_2+w_tr² eta_3, w_tr=z^(3t+r−1).
All w_tr are distinct and positive. Pair intersections have representatives
(uv,−u−v,1), with L(w) evaluating to (w−u)(w−v). Diagonal representatives
(0,−w,1), (w²,0,−1), (−w,1,0) have line evaluations v(v−w), w²−v²,
v−w. These representatives differ from the defined cross products by
nonzero factors. Substitution into the displayed quadratic separators
also gives nonzero diagonal values. Thus the local, cross-block, and
coefficient-difference factors are all nonzero for every finite T. The
Lean-checked witness fixes z=2.

The exceptional product is consequently nonzero at this economic witness.
Its factors are polynomial in the normalized line coefficients, so composition
with the exponential economic map is real analytic on the full connected
domain Theta_T. The analytic identity theorem then makes the explicitly
defined region nonempty, open, and dense. These statements compile in
`StructuralGenericity`, and `StructuralCompleteness` packages the resulting
economic dimension theorem. No genericity claim is made on every arbitrarily fixed covariate or slope slice.

## Four periods: the source basis

At T=4 the proposed family has five groups: generation-order pairs
(1324,2314) and (1234,3214), each with three first-state indicators;
(1234,1324), (2134,2314), and (3124,3214), each with nine shared-prefix
indicator choices. This gives 33 moments.

At z=2 the exact script constructs C0 and K=Msrc diag(A_y), verifies
C0 K^T=0, and computes fixed nonzero 48- and 33-minors over the integers.
All three initial-state K matrices are checked externally. For the Lean
certificate, a second exact calculation instead selects 48 fixed polynomial
evaluations at positive integer effect pairs and 48 path columns. Together
with three fixed K minors, these matrices have explicit inverses modulo 11.
The formal kernel has checked both the primitive formulas and the inverse
identities; modular nonvanishing lifts to integer and real determinants.
The coefficient calculation remains useful discovery evidence, while this
evaluation certificate supplies the same restriction-rank lower bound.

The fixed minors define polynomials whose nonvanishing is open dense after
economic substitution. Universal source-moment validity plus these two rank
bounds gives the basis assertion for all three initial states. The source
validity, concrete certificates, dimension-sandwich argument, economic
witness, analytic genericity, and final finite theorem all compile. The
axiom audit and independent statement audit both report **PASS**. The first
clean finite rebuild also passed, including a fresh axiom audit. The finite
milestone is accepted.


## Formal statements and limits

`PanelMoments.three_choice_four_period_generic_completeness` proves the
finite source-family basis. Separately,
`PanelMoments.StructuralCompleteness.three_choice_generic_moment_dimension`
proves the arbitrary-period dimension on the explicit joint economic domain.
Both quantify over every initial state. Their generic regions are separate
sufficient sets, with no asserted inclusion between them. The Lean formula
places the nonnegative correction before natural subtraction, and the additive
identity is proved first.

The only axioms reported for both main theorems and their audited dependencies
are `propext`, `Classical.choice`, and `Quot.sound`. All project proof sources
are checked for proof holes, custom axioms, and native computation oracles.
The finite certificates are verified by the kernel; the arbitrary-period
argument uses the proved induction rather than an unbounded numerical pattern.
Neither theorem establishes parameter identification, estimator efficiency,
priority, a measure-zero exceptional set, or genericity on every fixed slice.

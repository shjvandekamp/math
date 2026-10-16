# Appending a copy of the last old time

**Status: audited paper identities and a partial boundary rank result.
No all-length independence theorem.**

Use the actual local E/F source list and prefix map from
[SOURCE24_PREFIX_PENCIL.md](SOURCE24_PREFIX_PENCIL.md). There are q old
blocks, with q the last in the prescribed increasing order, and a new
block n=q+1. Put N_q=9q(q−1)+3q. This note studies A_n=A_q, with
generic old geometry. It concerns rational rows with coalescing poles;
the generic W0_n and transverse-coordinate dimensions cannot simply
be specialized to this collision.

## The inherited source graph survives the collision

Consider the rational append map

\[
 T_q(R,I)=RK_q+I(I-K_q),
 \qquad R\in W_{0,q},\ I\in\mathrm{Prefix}_q.
 \tag{LC1}
\]

Its kernel is exactly

\[
 \ker T_q
 =\operatorname{span}\{(-E_{qa},X_a e_aK_q):a=0,1,2\}.
 \tag{LC2}
\]

For the proof, write I=j diag(X), g=j A_q^(-1). The equation T_q=0
forces R_c=X_c j_c−L_qc g_c. On an old line i=(t,a), let c_i be
the vector of coefficients of X_a/L_i in j. Output-coordinate
divisibility at P_ic forces (c_i A_q^(-1))_c=0 for c different
from a. The old matching condition also forces its a-component
to vanish unless t=q: L_qa(P_ia) is nonzero in the former case,
whereas L_qa=L_i in the latter. Thus the only possible pole terms
in I are d_a X_a e_a K_q. Their corresponding rows are −d_a E_qa.
Subtracting these explicit solutions leaves constant j; coordinate
divisibility forces each component of j A_q^(-1) to vanish. This
proves (LC2), including the absence of further constant solutions.

Under the explicit shorter-length source-independence premise,
I_old(E_qa)=E_qa. Hence the graph defect of each kernel generator is

\[
 I_{\rm old}(-E_{qa})-X_a e_aK_q=-X_a e_a.
 \tag{LC3}
\]

These three diagonal polynomial prefixes are independent. Therefore
the kernel in (LC2) meets the actual old source graph trivially:
the N_q copied-old sources remain independent at the collision.
Moreover, the graph defect modulo those three polynomial prefixes
is well-defined on im(T_q), despite the ambiguity in its ambient
preimage. This does not identify im(T_q) with a generic transverse
kernel at the collision.

## All exact source collisions and the first derivatives

Write C(F_tsab) for an old pair source evaluated at the new length;
its word still contains the terminal K_n. At K_n=K_q,

\[
 E_{na}=E_{qa},\qquad
 F_{n,s,a,b}=C(F_{q,s,a,b})\quad(s\ne q),
 \tag{LC4}
\]
\[
 F_{t,n,a,b}=C(F_{t,q,a,b})\quad(t\ne q),\qquad
 F_{n,q,a,b}=F_{q,n,a,b}.
 \tag{LC5}
\]

These are whole-row identities with the actual word order. For
example, for t different from q, let T be the increasing product
omitting t and q and let P_tab=X_a K_t(a,b)e_b. Then the difference
in (LC5) is exactly

\[
 F_{t,n,a,b}-C(F_{t,q,a,b})
   =P_{tab}(K_q T K_n-K_n T K_q).
 \tag{LC6}
\]

The two words agree when the last matrices agree. Let W_ab denote
the nine common rows F_(q,n,a,b)=F_(n,q,a,b). A constant invertible
column change therefore gives N_q+9 potentially nonzero leading
columns [C,W], and the following 18q−6 vanishing differences:

- the three differences E_n−E_q;
- 9(q−1) shared-new differences in (LC4);
- 9(q−1) first-new differences in (LC5);
- the nine differences F_(n,q)−F_(q,n).

In particular the collision has leading rank at most N_q+9,
not N_q+9q. If [C,W] is independent, its first derivative on those
18q−6 exact coefficient relations is the next rank test. A larger
kernel of [C,W] would require differentiating that kernel as well.

The apparent cubic poles in these derivatives cancel. For example,
write dot K for the derivative of K_n at K_q. Differentiating (LC6)
gives P_tab(K_q T dot K−dot K T K_q). Near z=L_qa, write
K_q=R/z+S+... and dot K=−dot L_qa R/z²+V/z+.... The z^(-3)
terms are identical and cancel. The other vanishing differences
have the same cancellation by the product rule, including the
derivative of the copied-old terminal K_n. Thus third-order poles
cannot be used as independent leading pivots in this test.

## Three new leading directions are generically independent

Put Q=K_1...K_(q−1), and v_a=A_q(a,:)diag(X). Every L_qa^(-2)
coefficient of an appended ambient row T_q(R,I) is parallel to v_a:
only the final K_q creates the second pole. The diagonal surviving
row has instead

\[
 W_{aa}=\frac{A_q(a,a)X_a^2}{L_{qa}}e_a(I-K_q Q),\qquad
 [L_{qa}^2 W_{aa}]_{L_{qa}=0}
    =-A_q(a,a)X_a^2v_a Q.
 \tag{LC7}
\]

If v_a Q is not parallel to v_a as a rational row on L_qa, this
column is nonzero modulo im(T_q). Each of the other two diagonal
rows has no double pole on that line. Thus the three diagonal W
columns are independent modulo the entire appended ambient image.

Here is a common-G algebraic witness proving that nonparallelism
is generic for every q>=2. Take

\[
 H=\begin{pmatrix}
 5/8&1/8&1/4\\1/8&5/8&1/4\\1/4&1/4&1/2
 \end{pmatrix},\qquad X=(1,1,1).
 \tag{LC8}
\]

Set all old times except q to (1,1), so their kernels are H and
Q=H^(q−1). Its two zero-sum eigenvalues are 1/2 and 1/4; their
(q−1)-st powers remain distinct. For each fixed a, choose q-time
(u,v) on H_a0+H_a1 u+H_a2 v=0. The row
v_a=(H_a0,H_a1 u,H_a2 v) has fixed nonzero first coordinate and
varies along an affine line in the zero-sum plane. It is not
contained in either eigenline. Avoiding finitely many points
therefore makes v_a Q nonparallel to v_a, while u, v, A_q(a,a)
and the other two q-line values are nonzero.

These q-times may be negative; this is an algebraic nonvanishing
witness, not a positive specialization. Normalizing the first
column of H by row scaling fits the prescribed common-G form and
does not change the kernels. Repeated other-old times cause no
denominator failure at this X. Clearing denominators gives a nonzero
polynomial for each a. Their product can then be combined with the
old-independence and generic geometry opens in the same parameter
ring, which also has positive real witnesses. Consequently, under
the shorter-length premise, the generic coalescent leading rank obeys

\[
 N_q+3\ \le\ \operatorname{rank}[C,W]\ \le\ N_q+9.
 \tag{LC9}
\]

The six other W columns and the first derivative rank are not settled
by (LC9). Full rank at isolated finite lengths would still require
a structural proof before giving an induction for arbitrary q.

## Finite first-jet certificates

The bounded verifier
[source24_last_time_coalescence.py](../exploration/source24_last_time_coalescence.py)
and its [saved certificate](../exploration/source24-last-time-coalescence-results.json)
evaluate the actual rows and derivatives over F_1000003. They use
G=((1,1,1),(1,30,10),(1,3,2)) and old times (8^t,8^(2t)), t=1,...,q.
Both sides of every difference in (LC4)--(LC5) are differentiated,
including the copied-old terminal K_n. The initial u-only direction
is retained; the follow-up uses

\[
 u_n=u_q(1+\varepsilon),\qquad
 v_n=v_q(1+2\varepsilon).
 \tag{LC10}
\]

| New-time direction | q | Copied-old rank | Rank of [C,W] | Rank with first jets | Full minor modulo 1000003 |
|---|---:|---:|---:|---:|---:|
| u only | 4 | 120 | 129 | 193 of 195 | — |
| Relative (1,2) | 4 | 120 | 129 | 195 of 195 | 23466 |
| Relative (1,2) | 5 | 195 | 204 | 288 of 288 | 597175 |

All three bases [C,W] have full column rank. The listed vanishing
differences consequently form the complete leading coefficient kernel.
The combined matrices use leading values of [C,W] and first derivatives
of these differences, not independently stacked values and derivatives
of the same source columns. The u-only deficiency is a sampled rank
lower bound; it is not an upper bound on rational-function rank or a
source-dependence certificate.

All six matching and same-block basepoints have nonzero projective
velocity in the two relative-flow fixtures. This geometric check does
not prove the source rank. Independent ordinary source evaluation,
ordinary product-rule differentiation, and the exact copied-append
formula check the actual calculations at three effect points. Every
collision identity is checked at every evaluation point. Matrices,
row and column labels, selected nonzero minors, hashes, and parameters
are saved. The primary and an independent reviewer read the verifier;
the reviewer did not rerun its arithmetic.

In the saved transformed column order and selected pivot-row order,
the two full minors have exact leading epsilon orders 66 and 84,
respectively. Each of the 18q−6 difference columns is zero at zero,
so its factor epsilon can be extracted; the displayed nonzero minor
is the coefficient left at epsilon zero. The original source column
order can change its sign. Nonvanishing modulo the prime, with all
denominators invertible, proves a nonzero rational coefficient and
hence finite positive generic source-rank witnesses near the collision.
It does not prove the same leading coefficient nonzero for arbitrary q.

To reproduce without replacing the saved three-case certificate, use
the project root as the working directory:

```sh
nice -n 19 python3 exploration/source24_last_time_coalescence.py \
  --output /tmp/source24-last-time-coalescence.json
nice -n 19 python3 exploration/source24_last_time_coalescence.py \
  --generic-followup --output /tmp/source24-last-time-coalescence.json
```

The follow-up took 3.97 seconds with peak RSS 68,976,640 bytes including
JSON serialization. Its internal pre-serialization RSS was 39,321,600
bytes. Each process is guarded at 28 seconds and 95 MiB. No Lean
certification of these finite minors is claimed.

The concrete uniform obligations are now: prove all nine W columns
independent modulo C generically, and prove that the 18q−6 actual
vanishing-column derivatives in a suitable common-G direction are
independent modulo [C,W]. The successful two finite cases motivate
that target but do not discharge either obligation at arbitrary q.

## Fixed generator and transverse squared-pole blocks

For a relative direction D=diag(0,τ,ν), put H=G D G^(-1).
The first column of G is 1, so H1=0. Writing L=A_q X gives
dot L=HL. Direct differentiation of K=diag(L)^(-1)A_q diag(X)
then gives the right logarithmic derivative

\[
 B:=\dot K K^{-1}
   =\operatorname{diag}(L)^{-1}H\operatorname{diag}(L)
       -\operatorname{diag}((HL)_a/L_a).
 \tag{LC11}
\]

Thus H is independent of the q-time factors. For a first-new
difference in (LC6), with T the increasing product omitting t and q,
its derivative multiplied on the right by K^(-1) is
p_(t,a,b) e_b [KT,B]. This is an effect-dependent commutator, not a
constant change of source coefficients.

Fix a q-line c and write z=L_qc. At an ordinary point on it, expand
K=R/z+S+O(z), dot K=−ell R/z²+V/z+O(1), where
R=e_c v_c, v_c=(A_q(c,j)X_j)_j, and ell=dot L_qc on the line.
Set Ω=V+ell S. The cubic terms in KT dot K−dot K TK cancel;
the squared-pole coefficient is RTΩ−ΩTR. Modulo the line spanned
by v_c, the row e_b therefore has coefficient

\[
 p_{t,a,b}\,\delta_{bc}\,[v_c T\Omega].
 \tag{LC12}
\]

The whole ambient append image has squared-pole coefficient parallel
to v_c, so this transverse observation kills that image. It need
not kill the nine additional W_ab leading source columns. In
particular, (LC12) alone does not give pivots modulo the full base
[C,W_ab].

For d≠c choose the column λ_d=diag(X)^(-1)A_q^(-1)e_d.
Then v_c λ_d=0 on the line and Kλ_d=e_d/L_qd. Retaining the
variation of λ_d in the Laurent expansion gives
Ωλ_d=H_cd e_c+(ell/L_qd)e_d. Consequently the nonzero b=c block
in (LC12), after this transverse scalar observation, consists of

\[
 p_{t,a,c}\left[
 H_{cd}(v_cT)_c+\frac{\dot L_{qc}}{L_{qd}}(v_cT)_d
 \right],\qquad t<q,\quad a=0,1,2.
 \tag{LC13}
\]

All identities are at generic points where the other displayed
denominators and coordinates are nonzero. Each c gives 3(q−1)
candidate functions; their joint rank is a new obligation.

There is a particularly simple algebraic specialization. Let C be
the directed cycle matrix and choose the Fourier columns of G in
the order of C's eigenvalues 1,ω,ω², where ω³=1 and ω≠1.
With (τ,ν)=(ω−1,ω²−1), one has H=C−I. If d is the successor
of c and e is the remaining state, then on L_qc=0,
dot L_qc=L_qd. Because v_cT is zero-sum, (LC13) becomes

\[
 -p_{t,a,c}(v_cT)_e.
 \tag{LC14}
\]

The Fourier matrix has nonzero entries, determinant, and two-by-two
minors. Independent generic time factors can avoid the remaining
line incidences. This is a complex algebraic specialization, not a
positive economic fixture. A nonzero minor proved here would
establish generic common-G nonvanishing after clearing denominators;
generic old-source independence cannot simply be assumed at this
particular G.

The fixed-terminal simplification also has a concrete limitation.
For just two other blocks, let g_a=A_q(c,a) and
f_(t,a)=p_(t,a,c)(v_c K_other)_e. Direct multiplication gives

\[
 \sum_a\frac{g_a A_1(a,e)}{A_1(a,c)} f_{1,a}
 =\frac{X_c}{X_e}(v_cK_1)_e(v_cK_2)_e
 =\sum_a\frac{g_a A_2(a,e)}{A_2(a,c)} f_{2,a}.
 \tag{LC15}
\]

These are nonzero constant coefficients, so the six functions are
dependent. This identity holds for the fixed-terminal family even
without Fourier G. It does not settle the required longer deletion
blocks or the complete coalescent jet family. In particular, one
cannot infer (LC14)'s independence from nonzero individual endpoints
or an unrelated moved-word rank theorem.

Writing m=q−1, Δ_t=∏_a L_ta, B_t=Δ_t K_t and D_old=∏_t Δ_t
gives a useful exact binary-polynomial form on L_qc=0. Put

\[
 N_t=\frac{v_c B_1\cdots B_{t-1}B_{t+1}\cdots B_m e_e}{X_e},
 \qquad f^{\rm cub}_{ta}=X_a\prod_{b\ne a}L_{tb}.
 \tag{LC16}
\]

Output-coordinate divisibility makes N_t a polynomial of degree
3m−3. Dividing the column p_(t,a,c)(v_cT)_e by the common factor
X_c X_e and the nonzero constant A_t(a,c) gives
N_t f^cub_(ta)/D_old. Thus the precise fixed-terminal target is
independence of 3m actual degree-3m binary forms N_t f^cub_(ta).
The N_t retain their ordered matrix-product constraints. For m=2,
N_1 lies in the span of the second block's three cubics and N_2
in the first block's span; the shared product N_1N_2 explains
(LC15). That argument does not extend by appending an arbitrary
prefix, because its required coefficients would depend on X.
Finite-residue observations can miss a constant rational function,
so independence of these forms is also distinct from independence
of their pole-coordinate columns.

The bounded [cyclic probe](../exploration/source24_cyclic_transverse_probe.py)
and [saved exact output](../exploration/source24-cyclic-transverse-probe-results.json)
use p=1000003, Fourier G, old times (2^t,5^t), and q-time (97,193).
For each c=0,1,2, the evaluation ranks are:

| m=q−1 | Columns | Rank for every c |
|---|---:|---:|
| 2 | 6 | 5 |
| 3 | 9 | 9 |
| 4 | 12 | 12 |
| 5 | 15 | 15 |

For m=2 the separate exact relation supplies the upper bound.
The other ranks are full finite witnesses, not an all-m proof.
The script checks the cycle orientation, actual completed-word
residues, and the nine cancelling numerator pairs in (LC15).
It saves evaluation matrices, points, labels, hashes, and nonzero
minors. One run took 0.16 seconds with peak RSS 15,335,424 bytes;
the primary reviewed the code without a second arithmetic run.

## Six special jets are uniformly independent modulo the full base

The same-block q-line intersections give a different observation
that kills the entire leading base, including all nine W_ab.
Fix P_cd=L_qc∩L_qd, c≠d, and use local coordinates z=L_qc,
w=L_qd. Assume all coordinates of P_cd are nonzero and all other
old lines avoid it. Then Q=K_1...K_(q−1) is regular and invertible
there. Every column of [C,W] has total pole order at most two under
(z,w)↦ρ(z,w): each term contains at most two q/new factors.

For the special difference D_ab=F_(n,q,a,b)−F_(q,n,a,b), its
actual derivative is

\[
 D'_{ab}=\dot p_{qab}e_b(I-K_qQ)+p_{qab}e_b\dot K_qQ.
 \tag{LC17}
\]

Set n_ab=A_q(a,b)X_aX_b, evaluated at P_cd. Its homogeneous
degree-minus-three principal part, for the two relevant columns, is

\[
 [D'_{cd}]_{-3}
  =n_{cd}\left(\frac{\dot L_{qc}}{z^2w}
                    -\frac{\dot L_{qd}}{zw^2}\right)v_dQ,
 \qquad
 [D'_{dc}]_{-3}
  =-n_{dc}\left(\frac{\dot L_{qc}}{z^2w}
                    -\frac{\dot L_{qd}}{zw^2}\right)v_cQ.
 \tag{LC18}
\]

All coefficients and rows on the right are evaluated at P_cd.
The other special columns have zero degree-minus-three part at
this pair. For a=b the apparent single-line cubic pole cancels.
The rows v_c,v_d are independent zero-sum rows because A_q diag(X)
is invertible; multiplication by Q preserves their independence.
Both n_cd and n_dc are nonzero.

If 0,τ,ν are pairwise distinct, dot L_qc and dot L_qd cannot both
vanish at P_cd. Otherwise X and diag(0,τ,ν)X would lie in the
same one-dimensional common kernel of rows c,d of A_q and hence
be proportional. With all three coordinates of X nonzero, this
would force 0=τ=ν. At each pair, select the coefficient of z^(-2)w^(-1)
when dot L_qc is nonzero, or of z^(-1)w^(-2) otherwise. This gives
a two-dimensional observation with an invertible two-column block.

The three unordered pairs therefore supply six independent
observations and a block-diagonal invertible matrix on the six
off-diagonal special jets. All observations annihilate [C,W].
Consequently these six jets are independent modulo the **entire**
leading base for every q≥2 on the stated geometry open. This result
requires no old-source independence premise. Combined with (LC9),
under that premise the leading-plus-first-jet rank is at least N_q+9.

Other jet columns may have nonzero values under these six
observations. They must be corrected by the six special pivots
before subsequent residue tests. If all nine leading W columns
are independent modulo C, this removes six of the 18q−6 derivative
columns and leaves 18q−12 corrected columns to settle. The formulas
(LC13)--(LC16) alone do not account for that correction, so their
finite ranks cannot be added directly to this six-dimensional gain.

## Matching observations complete a twelve-jet local block

The following extension was proposed in the
[Pro coalescence investigation](https://chatgpt.com/c/6ad18533-9628-83eb-ace3-46e2a2400a7e)
and checked locally by the primary and an independent mathematical
reviewer. It adds the three local E derivatives and the three diagonal
special derivatives to the six pivots above. It remains a paper proof.

Let M_a=L_qa∩{X_a=0}, and assume every other old denominator is
nonzero there. In the chart X_j=1, j=a+1 modulo 3, use x=X_a as
coordinate on L_qa. Define the divided double coefficient and its
linear Taylor observation by

\[
 \widehat\rho_a(H)
   =\left.L_{qa}^2 H\operatorname{diag}(X)^{-1}\right|_{L_{qa}=0},
 \qquad \Theta_a(H)=[x^1]\widehat\rho_a(H).
 \tag{LC19}
\]

Keep output components a,j of Θ_a. Coordinate divisibility makes
the divided expression regular near M_a for the actual base and
jet rows. On every base column, it is O(x²). Indeed a double q-line
pole in a completed source term requires two visits to state a at
the two q/new positions. Each visit supplies an incoming X_a; an
initial visit instead uses the exterior X_a. Division by the final
output coordinate removes the final outgoing factor, not either
incoming factor. Equivalently, for a copied append row the relevant
old residue's a-component has both its incoming and output X_a,
and the final appended kernel supplies a separate final output.
For W_aa the factor A_aa X_a² is explicit. Other W_ab have no
double pole on that line. Thus Θ_a annihilates the entire base.

Write Z_a=−X_a e_a dot K and S_ab=D'_ab from (LC17), and let
d=(0,τ,ν), D=diag(d). Exact expansion gives

\[
 Z_a=\frac{X_a\ell_a v_a}{L_a^2}
              -\frac{X_a v_aD}{L_a},
 \qquad
 S_{aa}=A_{aa}X_a^2\left[
 \frac{d_a e_a}{L_a}
 +\frac{v_a(D-d_a I)Q-\ell_a e_a}{L_a^2}\right].
 \tag{LC20}
\]

Here L_a=L_qa and ell_a=dot L_qa. Since q≥2, Q is a nonempty
product, so Q diag(X)^(-1) is regular at M_a: the final old kernel
provides every output-coordinate factor. Hence the first numerator
term of the divided double coefficient of S_aa remains O(x²).
The other term loses one X_a on division of its a-component. Therefore

\[
 \Theta_a(Z_a)=\ell_a(M_a)A_q(a,:),\qquad
 \Theta_a(S_{aa})=-A_{aa}\ell_a(M_a)e_a.
 \tag{LC21}
\]

Different q-lines give zero on these six columns. The two-component
block on (Z_a,S_aa) has determinant A_aa A_aj ell_a(M_a)².
Writing A_q(a,:)=(1,r_a,s_a), the three chosen charts give
ell_0(M_0)=(τ−ν)r_0, ell_1(M_1)=νs_1, ell_2(M_2)=−τ.
Their three determinants therefore multiply to

\[
 \tau^2\nu^2(\tau-\nu)^2 r_0^3 r_1 s_1^3 s_2\ne0.
 \tag{LC22}
\]

The six same-block observations in (LC18) annihilate every Z_a
and S_aa. The matching observations may see the off-diagonal S,
but this creates only a lower off-diagonal block. Combining the
six same-block scalar observations and the six matching observations
as Φ, and ordering
J=(S_01,S_10,S_02,S_20,S_12,S_21,Z_0,S_00,Z_1,S_11,Z_2,S_22),
the twelve-square matrix Φ(J) is block triangular and invertible.
It annihilates **every** base column. Thus all twelve local jets
are independent modulo [C,W], uniformly for q≥2 on the geometry
open and for distinct relative weights. Old-source independence
is not needed for this local theorem.

This gives a fully specified constant-in-X correction

\[
 \Pi H=H-J\,\Phi(J)^{-1}\Phi(H),\qquad
 \Pi B=B,\quad \Pi J=0.
 \tag{LC23}
\]

The off-diagonal matching block is retained by the inverse; it is
not discarded. Only the 9(q−1) shared-new jets and 9(q−1) first-new
jets remain after this correction. There is an exact rank identity

\[
 \operatorname{rank}[B,D']
 =12+\operatorname{rank}[C,W,\Pi D'_{\rm shared},\Pi D'_{\rm first}].
 \tag{LC24}
\]

Under shorter-source independence, (LC9) gives independent C and
the three diagonal W, so the established lower bound strengthens
to N_q+15. Modulo their span, full first-jet independence is exactly
the independence of the six off-diagonal W and the 18(q−1) corrected
jets: 18q−12 specified columns. This retains the six leading W
directions as an open obligation rather than presuming full base
rank. Uniform nonvanishing of this remaining quotient is unproved.

## A uniform vector deletion lemma and its projection limit

There is a separate uniform induction on the fixed terminal q-line.
For m earlier blocks, let v=v_c and T_t be their increasing product
omitting t. The 3m vector rows

\[
 \frac{X_a}{L_{ta}}\,vT_t,\qquad 1\le t\le m,\quad a=0,1,2,
 \tag{LC25}
\]

are generically independent over coefficients constant in the effect
coordinate. This uses the common-G model and requires no source-family
independence premise. For m=1, their three distinct simple poles on
the fixed q-line isolate the three coefficients.

Append an earlier block n after the existing m blocks, keeping the
terminal q-line fixed. In a relation, the old deletion rows become
(X_a/L_ta)vT_t K_n; the three new rows are (X_a/L_na)vP_old.
Multiplication on the right by K_n^(-1) removes K_n from every old
term. At the three new intersections, these terms have no pole.
The residue of the a-th new term is its coefficient times
X_a vP_old K_n^(-1).

The inverse is regular of rank two at L_na=0, with left kernel
spanned by v_na. Its displayed row is generically nonzero. To see
this within the common-G parameter family, fix a point X on the
terminal line with all coordinates nonzero and all earlier kernels
invertible. The fixed row vP_old is nonzero. Vary (u_n,v_n) subject
to L_na(X)=0: v_na varies along a nonconstant affine line in the
zero-sum plane with fixed nonzero first coordinate X_0. That affine
line cannot lie in the fixed one-dimensional span of vP_old.
Each of the three residue conditions is therefore a nonempty
algebraic open. Their product is nonzero, so all new coefficients
vanish generically. Old independence persists under adjoining the
new time parameters, completing the induction.

This lemma was independently audited. It does not imply scalar
deletion independence: (LC15) is an explicit counterexample to that
inference at m=2. Nor does it prove preservation under Π or after
quotienting by the leading W directions. Recovering a suitable vector
observation from the actual corrected incoming/shared rows is a
concrete next step.

## Two directions give a growing one-direction lower bound

The vector lemma does give a uniform rank bound without claiming
that a scalar projection preserves independence. Fix the transverse
observation O consisting of the three squared-q-line coefficients,
each contracted with λ_d for a fixed d≠c. The choice of O does not
depend on the perturbation direction. Write m=q−1.

On L_qc, choose the third state e and put t=L_qe/L_qd. Since
ell_c=H_cd L_qd+H_ce L_qe there, (LC13) acts on the two independent
coordinates ((v_cT)_c,(v_cT)_d) by the row
(H_cd,H_cd+t H_ce). For the two coordinate directions τ and ν,
the determinant of these two rows is

\[
 t\,G_{c1}G_{c2}
 \det (G^{-1})_{\{1,2\},\{d,e\}}
   =\pm t\,\frac{G_{c0}G_{c1}G_{c2}}{\det G}\ne0.
 \tag{LC26}
\]

The inverse-minor identity gives the equality, and the displayed
factors are nonzero rational functions on the generic line. Any
two independent direction pairs give the same conclusion. In
particular take δ_1=(1,2), δ_2=(1,3), so both also satisfy the
twelve-pivot hypotheses.

The stacked uncorrected incoming observations therefore have
full 9m column rank: each of the three b=c sectors recovers its
3m vector deletion columns from (LC25). This assertion concerns
one common coefficient vector across the two directions. It does
not imply that a single-direction matrix pencil has full rank.

For each direction i, quotient the observation target by
O(span(B,J_i)), where J_i is its actual twelve-column local jet
family. The observation kills C and every off-diagonal W; only
three diagonal W may survive. It also kills all three Z_a, whose
squared coefficient is X_a ell_a v_a. Only nine special S columns
may survive. Hence each quotient removes at most 3+9=12 dimensions.
The two quotient targets together remove at most 24, leaving
stacked incoming rank at least max(0,9m−24).

Let r_i be the incoming source rank modulo span(B,J_i). The
observed quotient ranks are no larger than r_i. Thus

\[
 r_1+r_2\ge9m-24,\qquad
 \max_i r_i\ge\max\left(0,\left\lceil\frac{9m-24}{2}\right\rceil\right).
 \tag{LC27}
\]

The twelve local classes are independent modulo B, so they can
now be added: the incoming ranks in (LC27) were measured **after**
quotienting by those classes. For at least one of the two directions,
and therefore for a generic direction by nonvanishing of that minor,

\[
 \operatorname{rank}[B,D']-\operatorname{rank}B
 \ge\max\left(12,\left\lceil\frac{9(q-1)}2\right\rceil\right).
 \tag{LC28}
\]

This argument never adds the uncorrected incoming rank to the
twelve pivots. It retains both direction-dependent correction
spaces and their possible intersections with the base. All generic
conditions used above can be intersected in the same common-G
parameter field.

Combining with the shorter-source premise and (LC9) gives

\[
 \operatorname{rank}[B,D']
 \ge N_q+3+\max\left(12,\left\lceil\frac{9(q-1)}2\right\rceil\right).
 \tag{LC29}
\]

For q=4 this is N_q+17; for q=5 it is N_q+21. A corresponding
minor of the actual new source family has a nonzero leading
epsilon coefficient after extracting one epsilon from each
selected vanishing column, so this is also a conditional generic
source-rank lower bound. It is strictly weaker than the required
full rank N_(q+1)=N_q+18q+3. The two-direction argument and its
quotient loss count were independently audited; they are not Lean
formalized and do not prove a regular full-rank pencil.

## A one-component prefix for the six leading off-diagonal rows

For a≠b let i be the third state. Subtract a known copied-old
column from the surviving row:

\[
 \delta_{ab}=W_{ab}-C(F_{q,1,a,b})
      =p_{qab}e_b(QK-KQ),\qquad
 J_{ab}=\delta_{ab}K^{-1}=p_{qab}e_b(Q-KQK^{-1}).
 \tag{LC30}
\]

The index 1 is the first earlier block, so its remaining suffix is
exactly Q. An ambient preimage of δ_ab can be chosen with prefix
in just the third row direction:

\[
 I_{ab}=h_{ab}v_i,\qquad
 R_{ab}=J_{ab}+h_{ab}(v_i-L_i e_i),\qquad
 T_q(R_{ab},I_{ab})=\delta_{ab}.
 \tag{LC31}
\]

Here h_ab lies in the scalar prefix space J_q=span{1,X_d/L_td}.
It is recovered by the old-line interpolation on axis X_i=0
applied to g_i=(J_ab)_i/L_i, retaining all divided matching data
at old lines other than (q,i). The coefficient of X_i/L_i is
free and can be set to zero. Ordinary axis restriction alone does
not determine the matching coefficients with state i.

For the ambient verification, J_ab has no coordinate poles.
Its a,b components already satisfy coordinate divisibility and
the old matching conditions. The prefix p_qab supplies X_aX_b;
at an earlier pole in state a or b the completed path supplies
an additional incoming or terminal factor. At the q matching
points, the corresponding output factor of K^(-1) cancels the
potential q pole in the affected component. Thus the interpolation
is needed only for component i. It makes
R_i=L_i(g_i-h_ab)+A_q(i,i)X_i h_ab coordinate-divisible and matching.
The other two corrected components preserve these properties,
since every line residue of h_ab is proportional to that line's
state coordinate.

The possible same-block double residue at P_ab also vanishes:
K^(-1)(P_ab)=1 e_i^T, while v_bQ is zero-sum. The added term in
(LC31) has at most simple old poles, so it adds no same-block
double residue. These checks put R_ab in the full old ambient
space W0_q, not just a space of rows with partial axis conditions.

There is a useful pole distinction. The row δ_ab generally has a
q,i pole. J_ab has no such pole, but g_i may have the term
p_qab Q_bi/L_i. Its numerator contains X_i, so its ordinary axis
restriction vanishes, and multiplication by L_i in R_i cancels
that term. This is why the q,i prefix coefficient is free; an
asserted absence of the q,i pole in δ_ab would be false.
Changing h_ab by c X_i/L_i changes (R_ab,I_ab) by the kernel pair
(−c E_qi,c X_i e_iK), whose source-graph defect is −c X_i e_i.

The construction and these local conditions were independently
audited. It does not assert copied-source membership: the equation
I_old(R_ab)=I_ab, up to the known constant-prefix ambiguity, still
involves the actual old source graph.

Under shorter-source independence, the source-graph defect from
(LC3) identifies im(T_q)/span(C) with the prefix space modulo its
three constant diagonal rows X_i e_i. Its dimension is 9q.
Indeed the ambient kernel changes the defect by precisely those
three constants; if a defect is constant, that kernel adjustment
makes it zero and the row belongs to the copied-old source graph.
The three diagonal W are independent modulo all of im(T_q), while
every off-diagonal δ_ab belongs to im(T_q). It follows that all
nine W are independent modulo C exactly when the following six
columns have rank six:

\[
 \left[
 \operatorname{ResPrefix}_{\rm old}
       \bigl(I_{\rm old}(R_{ab})-h_{ab}v_i\bigr)
 \right]_{a\ne b},\qquad i=\{0,1,2\}\setminus\{a,b\}.
 \tag{LC32}
\]

This is a 9q-by-6 matrix with unambiguous pole coefficients.
Its nonvanishing remains open. The explicit one-component prefix
reduces the ambient recovery work, but does not compute the actual
old source expansion of R_ab.

## Exact finite recovery and a six-row minor to target

The [leading-prefix verifier](../exploration/source24_leading_prefix_probe.py)
and [saved output](../exploration/source24-leading-prefix-probe-results.json)
recover these actual preimages at q=4 and q=5, with the same prime,
G and time factors as (LC10). For each third state i, they solve
the actual appended E/F columns together with the 3q scalar h terms,
omitting only X_i/L_qi. The three systems have full column rank
132 at q=4 and 210 at q=5. Prefix coefficients are computed from
the recovered source coefficients by the defining formula, and
independently checked against the direct E/F prefix evaluation.

The preimage identities are checked as rational-function identities
over the finite field, rather than only at holdout sample points.
The common denominator D_old Δ_q clears each identity: every earlier
block occurs at most once and block q at most twice in every term.
It has degree 3q+3, so the cleared homogeneous row has degree
d=3q+4. On X_0=1 the translated triangular grid
(X_1,X_2)=(2+i,3+j), i+j≤d, is unisolvent. Its Newton basis has
diagonal entries i!j!, nonzero since p>d. All row denominators
are units on the grid. All three components of the six identities
vanish at its 153 points for q=4 and 210 points for q=5. This
proves the cleared polynomial identities at each parameter fixture.
The three prefix components are checked on the same grids as well.

The resulting 9q-by-6 matrix in (LC32) has rank six in both cases.
More specifically, at **each single old time t**, the six rows with
state a=0,1 and output b=0,1,2 already give a nonzero minor:

| q | Determinants in increasing time order, modulo 1000003 |
|---|---|
| 4 | 78978, 128152, 81259, 593672 |
| 5 | 414715, 154021, 55602, 234422, 439686 |

These are concrete finite witnesses for the smaller leading-rank
problem. They do not prove that the same six rows work for arbitrary
q. No sparse source expansion appears: every R_ab uses all N_q
old E/F coefficients and every h_ab uses all 3q allowed scalar terms
in both fixtures. In particular restricting the expansion to source
pairs involving q would be incorrect at these points.

The q-time prefix block does depend only on the sums of coefficients
of F_(q,s,a,b) and those of E_qa, together with the explicit q-time
h coefficients. First-q source columns have their prefix at their
other time. However the q-line residue equations couple these two
families, so this observation does not yet compute the required sums.
An all-q formula for this aggregation, or nonvanishing of one of the
displayed six-row minors, is the next leading-rank target.

The primary read the verifier and the clearing/unisolvence argument.
The extended run took 5.48 seconds and peak RSS 28,229,632 bytes;
the original q=4 coefficients were preserved exactly. This is an
external exact finite certificate, not a Lean-checked determinant.

## State symmetry fixes the direction in the growing rank bound

The [fixed-direction Pro calculation](https://chatgpt.com/c/6ad18b10-32fc-83eb-aab0-83a531433db2)
adds a symmetry argument to (LC26)--(LC29). It was checked locally
and independently audited. Normalize the transverse observation to
O_c(H)=L_d ρ_c(H)λ_d, d≠c. Since ∑_i L_i λ_i=1, the other
choice e gives its negative on a zero-sum row on L_c=0. For the
vector deletion row f_ta=(X_a/L_ta)v_cT_t, (LC13) becomes

\[
 \frac{O_c(V_{tac}(\delta))}{A_t(a,c)X_c}
   =H_{ce}L_e(f_{ta})_d-H_{cd}L_d(f_{ta})_e.
 \tag{LC33}
\]

The A_t(a,c) factor is a parameter-only column scaling; division
by X_c is a common invertible operation on this line's observation
space. Two independent directions therefore recover the same 3m
vector columns, m=q−1, as before. Let r(δ) be the generic rank
of all three incoming observation blocks for a fixed real direction.

State permutation π acts birationally on the same parameter family:
write z_t=(1,u_t,v_t) and set

\[
 G'_{ab}=\frac{G_{\pi(a),\pi(b)}}{G_{\pi(a),\pi(0)}},
 \qquad z'_{tb}=\frac{z_{t,\pi(b)}}{z_{t,\pi(0)}},
 \qquad X'_b=X_{\pi(b)}.
 \tag{LC34}
\]

The kernels conjugate by the permutation, all source columns
permute, and the time order stays fixed. If L'_c=s_c L_π(c), the
normalized observation changes by s_c² and possibly a sign. Here
s_c depends only on parameters, not X. First-order perturbation
weights permute and then subtract their new zeroth weight; adding
a common weight has no effect on the kernel derivative.

For a cycle, δ=(τ,ν) becomes δ°=(ν−τ,−τ), so r(δ°)=r(δ).
Their determinant is −(τ²−τν+ν²), nonzero for every nonzero real
δ. Stacked vector independence gives 9m≤r(δ)+r(δ°)=2r(δ).
Thus **every fixed real direction with 0,τ,ν distinct**, including
(1,2), gives the gain max(12,ceil(9m/2)) in (LC28), on its generic
old-parameter open. Existence of an unspecified good direction is
no longer needed.

There is a small further improvement. Fix c and exchange the other
two states. This preserves that state block's generic rank. The two
directions are independent precisely when
(d_d−d_e)(2d_c−d_d−d_e)≠0. If the weights are distinct and
(τ+ν)(2τ−ν)(2ν−τ)≠0, all three state blocks therefore have rank
at least ceil(3m/2). The blocks have disjoint column support, so
r(δ)≥3ceil(3m/2). Quotienting by O(span(B,J)) still loses at most
twelve dimensions. The exact Π correction vanishes in that quotient,
and its twelve pivots can then be added. For fixed δ=(1,3), or any
other such real direction, this proves

\[
 \operatorname{rank}[B,D']-\operatorname{rank}B
 \ge\max\left(12,3\left\lceil\frac{3(q-1)}2\right\rceil\right).
 \tag{LC35}
\]

Under shorter-source independence the total lower bound is N_q+3
plus (LC35). At q=4 it is N_q+18, one more than (LC29); at q=5
it remains N_q+21. The improvement by one occurs when q is even.
This argument concerns unrestricted independent time factors and
real directions. It need not preserve a prescribed time-factor
curve such as v_t=u_t², and does not assert all-length full rank.

## What last-block stripping can and cannot remove

The proof of (LC25) extends to independence modulo rows w(X)Q+g(X),
provided w,g have no poles at any earlier-line intersection with
the fixed terminal line. Multiply a proposed relation by K_m^(-1).
The full product becomes w K_1...K_(m−1); g K_m^(-1) remains
regular at the old intersections because the inverse kernel has
only coordinate denominators. Residues at the three m-th lines
isolate and kill the new deletion coefficients. Repeat backwards.
This proves the extended lemma, with the same nonzero residue
condition already established in (LC25).

It does not remove arbitrary right multipliers wQB. At a new line
L_ma=0 the relevant conjugated residue is

\[
 \operatorname{Res}(K_m B K_m^{-1})
    =e_a v_{ma}B K_m^{-1}\big|_{L_{ma}=0}.
 \tag{LC36}
\]

It vanishes exactly when v_ma B is proportional to v_ma. Inverting
the two-direction scalar observation can create rank-one right
multipliers from the actual W/S nuisance terms. They have no
established cancellation of (LC36). Thus the extended lemma alone
does not justify removing the twelve-dimensional loss in (LC35).

The analogous scalar deletion step also has a precise correction.
On the fixed terminal line let F lie in the old vector deletion
span, Q be the old full product, and b=(vQ)_e. For an appended
earlier time n, a scalar relation is
F K_n e_e+b∑_a c_na X_a/L_na=0. At P_na=L_na∩L_terminal,
assuming b(P_na)X_a(P_na)≠0, its new residues force

\[
 c_{na}=-\ell_a(F),\qquad
 \ell_a(F)=\left[
   \frac{A_n(a,e)X_e F_a}{X_a b}\right]_{P_{na}}.
 \tag{LC37}
\]

Hence the enlarged scalar family is independent exactly when
F↦F K_n e_e−b∑_a ell_a(F)X_a/L_na is injective on that old
vector span. Its new poles cancel by construction; its old residues
and pole-free remainder still need control. Old scalar independence
controls F_e, which is a different map. This append argument by itself
does not close the gap. A subsequent prepend induction proves the
scalar independence directly; see (SP1)--(SP15) in
[the scalar prepend proof](SOURCE24_SCALAR_PREPEND.md) and (LC47) below.
These two stripping observations and their limitations were independently
checked.

## Six vertex observations and the actual endpoint margins

The [six-column investigation](https://chatgpt.com/c/6ad1920e-6ff0-83ed-ad34-75fc2d0d413c)
produced the following conservation law, checked locally and independently.
It applies to the six off-diagonal leading columns in (LC30)--(LC32).
Retain their actual old-source preimages R_ab and prefixes I_ab=h_ab v_i,
where i is the third state. Let D_ab=I_old(R_ab)-I_ab and M its
9q-by-6 old-pole prefix matrix. For k different from j define

\[
 \mathcal V_{kj}(Y)=
   (Y_j/X_j)(e_k)-(Y_j/X_j)(e_j),\qquad
 (\mathcal O M)_{kj,ab}
 =\sum_t\left[
   \frac{M_{(t,k,j),ab}}{A_t(k,k)}
  -\frac{M_{(t,j,j),ab}}{A_t(j,j)}\right].
 \tag{LC38}
\]

The coordinate divisions are canceled before evaluating at the effect
vertices e_k; every row-form denominator is then nonzero. The observation
kills all polynomial diagonal prefixes, so V(D)=OM regardless of the
constant-prefix ambiguity. A nonzero determinant of this particular 6-by-6
observation matrix is sufficient for rank(M)=6; necessity is not asserted.

Write alpha_tsde^(ab) for the actual F coefficients of R_ab, and put
kappa_t,kj=A_t(k,j)/A_t(k,k). The only coefficients needed in these
observations of the actual completed tail are

\[
 \begin{split}
 S_{q-2,k}^{ab}&=\alpha_{q,q-1,k,k}^{ab}
                       +\alpha_{q-1,q,k,k}^{ab},\\
 S_{q-1,k}^{ab}&=\sum_{t\le q-2}
             (\alpha_{q,t,k,k}^{ab}+\alpha_{t,q,k,k}^{ab}),\\
 S_{q,k}^{ab}&=\sum_{\substack{t,s<q\\t\ne s}}\alpha_{t,s,k,k}^{ab},
 \qquad \sigma_k^{ab}=\sum_{\ell=q-2}^q S_{\ell,k}^{ab}.
 \end{split}
 \tag{LC39}
\]

These retain both orientations of the q-boundary terms. With
B_.ab=V(R_ab-I_ab), the exact identity is

\[
 \mathcal O M=B+\mathcal T S,\qquad
 (\mathcal T S)_{kj,ab}
   =\sum_{\ell=q-2}^q\kappa_{\ell,kj}S_{\ell,k}^{ab}
          -\sigma_j^{ab}.
 \tag{LC40}
\]

Indeed I_old(E)=E, so the E coefficients cancel from I_old(R)-R.
For a word with at least two kernels, ending in time ell, its j-th
component divided by X_j at e_k, k different from j, is kappa_ell,kj.
Every preceding kernel evaluates to the rank-one stochastic matrix
1 e_k. The scalar prefix X_d K_t(d,e) is nonzero at e_k only when
d=e=k, in which case it equals one. The actual suffix P_s with t
omitted ends at max([q] minus {t,s}); its three possible values give
exactly (LC39). At e_j the corresponding completed-tail value is sigma_j.
This proves (LC40), including the cancellation of every off-diagonal-state
F coefficient. It uses the actual ordered words, not arbitrary tails.

The known part also has a closed expression. Put

\[
 w^{(k)}=\frac{e_kA_{q-1}}{A_{q-1}(k,k)},\qquad
 \zeta^{(k)}
 =e_k-w^{(k)}A_q^{-1}
          \operatorname{diag}(A_q(0,k),A_q(1,k),A_q(2,k)),
\]
\[
 H_{i,k}^{ab}=A_q(i,i)h_{ab}(e_i)
       -A_q(i,k)\partial_{X_i}h_{ab}(e_k),\qquad k=a,b.
 \tag{LC41}
\]

For the column ab, the entries of B at rows
(ab,ba,ai,bi,ia,ib), respectively, are

\[
 \bigl(\kappa_{q,ab}\zeta_b^{(a)},\
       \zeta_a^{(b)},\
       H_{i,a}^{ab},\
       H_{i,b}^{ab},\
       0,\ 0\bigr).
 \tag{LC42}
\]

To check this, use R-I=J-h L_i e_i from (LC31). At e_k,
Q diag(X)^{-1}=1 w^(k), hence Q-KQK^{-1}=1 zeta^(k).
Also p_ab/X_b at e_a is kappa_q,ab, p_ab/X_a at e_b is one,
and p_ab has order two at e_i. Vertex vanishing of R gives
h(e_a)=h(e_b)=0. For output i, the regular expression for J_i
retains X_a X_b, so its X_i derivative at either e_a or e_b
is zero. This gives the two H entries in (LC42).

If h=h_*+sum_td h_td X_d/L_td, its needed values are explicit:

\[
 h(e_i)=h_*+\sum_t\frac{h_{ti}}{A_t(i,i)},\qquad
 \partial_{X_i}h(e_k)=\sum_t\left[
  \frac{h_{ti}}{A_t(i,k)}
  -\frac{h_{tk}A_t(k,i)}{A_t(k,k)^2}\right].
 \tag{LC43}
\]

In particular the coefficients h_ti, invisible in an ordinary restriction
to X_i=0, are retained. Adding c X_i/L_qi changes both terms defining
H by c, so (LC41)--(LC42) are independent of that gauge.
The ab/ba two-row, two-column block of B has determinant
zeta_b^(a) zeta_a^(b)
(G_ab G_ba/(G_aa G_bb)-1), generically nonzero. This is a block
of the known part, not a factor of det(OM).

The endpoint correction can itself fill all six observations. Hold the
three totals sigma_k fixed and use S_(q-2),k, S_(q-1),k as six
coordinates. For each origin state k, the two output rows j,l give
the 2-by-2 block with columns
(kappa_(q-2),kj-kappa_q,kj, kappa_(q-2),kl-kappa_q,kl)
and the corresponding q-1 differences. With observation order
(01,02,10,12,20,21), let
Delta=det[(1,u_t,v_t)] for t=q-2,q-1,q. The resulting determinant is

\[
 -\frac{\prod_{k\ne j}G_{kj}}{(G_{00}G_{11}G_{22})^2}
   \frac{\Delta^3}{\prod_{t=q-2}^q u_tv_t}\ne0
 \tag{LC44}
\]

on a nonempty generic positive common-G open. The three block signs
are +,-,+; their denominators are respectively 1, the product of
the three u's, and the product of the three v's. Thus even after
fixing the totals, the six formal boundary margins can change the
six observations arbitrarily. The margins of these particular R_ab
remain constrained by their actual source expansions. Dropping them
would invalidate a nonvanishing argument.

The reproducible check in
`exploration/source24_vertex_margin_probe.py` reads the saved q=4,5
rational-identity certificates without refitting. For each case it
independently computes OM from the prefix coefficients, TS from the
actual source coefficients, and B from h and the last two coefficient
tables. All 36 equalities (LC40), the twelve h vertex zeros, the
fixed-total determinant (LC44), and the three known pair-block factors
pass. Both observed matrices have rank six: their determinants modulo
1000003 are 889110 at q=4 and 73357 at q=5. Both known B matrices
also have rank six at these fixtures. Results are saved in
`exploration/source24-vertex-margin-probe-results.json`.
These are external exact finite-field certificates. A uniform proof
that the actual margin correction cannot cancel B is still missing.

First vertex jets alone cannot extract even one nonzero linear functional
of the nine margins for arbitrary actual old-source combinations. For
each k different from j, an off-diagonal source F_ts,k,j has exactly
one nonzero first vertex datum:

\[
 (F_{ts,k,j})_j/X_j\big|_{e_k}=\kappa_{t,kj}.
 \tag{LC45}
\]

All its other such data vanish, and all its margins (LC39) are zero.
The six off-diagonal choices therefore span the six first-jet
observations without changing any diagonal margin. Every prescribed
nine-vector of margins can first be realized by diagonal sources,
since all three terminal groups are nonempty, then have its first
vertex jets canceled by these six nuisance columns. This is a
statement about arbitrary source combinations. It does not exclude a
special relation for the six R_ab or recovery using higher jets or
pole data.

Higher jets admit an exact ordered recursion. At a fixed vertex e_k
write Pi_k=1 e_k and M_t=K_t-Pi_k. Then M_t Pi_k=0 and every
entry of M_t vanishes at e_k. For a word of length L,

\[
 K_{t_1}\cdots K_{t_L}
 =\Pi_k+\sum_{r=1}^{L-1}
       \Pi_k M_{t_{L-r+1}}\cdots M_{t_L}
       +M_{t_1}\cdots M_{t_L}.
 \tag{LC46}
\]

This follows by multiplication and M_t Pi_k=0. In the local ring
at e_k, a product of r such M's lies in the r-th power of the
maximal ideal. Thus a jet of degree d<L depends only on the last
d blocks. Applied to completed source tails, second jets introduce
terminal-pair aggregates of diagonal coefficients and terminal-single
aggregates of off-diagonal coefficients, because the latter prefixes
already vanish to first order at a vertex. The recursion retains these
additional terms; it does not yet provide a dual recovering (LC39)
without the actual old-source inverse.

## Full incoming observation rank and the stronger conditional bound

The independently audited [scalar prepend proof](SOURCE24_SCALAR_PREPEND.md)
now proves generic independence of all 3m scalar ordered-deletion
functions for every m>=3, augmented by the full-product scalar.
It uses one fixed positive common matrix, a preserving prepend limit,
three coordinate-axis principal parts, and an externally checked
10-by-10 integer-polynomial base determinant, nonzero modulo 17.
Its polynomial-observation extension starts at m=0 without a finite
base and applies to (LC33). The coordinate theorem handles the two
exceptional directions for that specialization. State permutations
and intersection of the three sector opens then give full uncorrected
incoming observation rank 9m for every fixed real direction whose
three rates are distinct, with m=q-1>=3.

The earlier nuisance quotient must still be retained. By (LC26)--(LC28),
O(span(B,J)) has dimension at most twelve: only the three diagonal W
columns and nine special S jets contribute. The three E jets are
invisible. Thus the incoming observations retain at least 9m-12
independent classes after this quotient. The exact correction by the
twelve local pivots disappears in that same quotient, and those twelve
pivots can subsequently be added. It follows that

\[
 \operatorname{rank}[B,D']-\operatorname{rank}B\ge9(q-1),
 \qquad q\ge4.
 \tag{LC47}
\]

Under shorter-source independence, rank B>=N_q+3 and hence the total
rank is at least N_q+9q-6. This improves (LC29) and (LC35), giving
N_q+30 at q=4 and N_q+39 at q=5. It does not remove the nuisance
loss by assumption and does not count the auxiliary full-product
scalar as an extra actual source column. Full independence would need
N_(q+1)=N_q+18q+3. In particular, the corrected shared jets, their
overlap with the incoming block, and the six off-diagonal leading
survivors still require proof. The statement concerns generic
independent time factors, not a prescribed curve such as v_t=u_t^2.

The augmented part supplies three additional actual shared-jet
directions. Let P_s start with K_s and then contain the other m
earlier blocks in increasing order, and set ell_c=dot L_qc. The
shared-new derivative is exactly

\[
 U_{s,a,b}=X_a\dot K(a,b)e_b(I-P_sK)
              +X_aK(a,b)e_bP_s\dot K.
 \tag{LC48}
\]

Its squared-pole transverse observation is zero on L_qc unless a=c.
For a=c, the same Laurent expansion as (LC12) gives

\[
 \frac{O_c(U_{s,c,b})}{A_q(c,b)X_c}
 =X_b\left[H_{cd}L_d(P_s)_{bc}
                +\ell_c(P_s)_{bd}\right]
                -\ell_cL_d(A_q^{-1})_{bd}.
 \tag{LC49}
\]

Indeed the transverse squared coefficient before contraction is
A_q(c,b)X_cX_b[e_bP_s Omega-ell_c e_b], modulo v_c.
Contracting with L_d lambda_d proves (LC49). Sum the actual three
columns over b. The last term cancels because
sum_b A_q(c,b)(A_q^(-1))_bd=0 for d different from c.
For s=1, P_1=Q, so the summed observation divided by X_c is
v_cQ[H_cd L_d e_c+ell_c e_d]. Since v_cQ is zero-sum and
ell_c=H_cd L_d+H_ce L_e on the line, this is precisely the
augmented full-product scalar in (SP13)--(SP15).

Consequently the incoming columns and the three shared sums
sum_b U_(1,c,b), c=0,1,2, have observed rank 9m+3. Applying the
same at-most-twelve-dimensional nuisance quotient and adding the
twelve actual local pivots strengthens (LC47) to

\[
 \operatorname{rank}[B,D']-\operatorname{rank}B\ge9(q-1)+3,
 \qquad
 \operatorname{rank}[B,D']\ge N_q+9q-3
 \quad\hbox{under shorter-source independence}.
 \tag{LC50}
\]

The totals are N_q+33 at q=4 and N_q+42 at q=5. These three
extra directions are actual sums of shared jets, not artificial
extra source columns. Two independent local derivations and an
independent audit checked the observation, cancellation and quotient
count.

There is also an exact ceiling on this observation's usefulness.
After dividing by X_c, all regular incoming/shared observations
with t,s among the m earlier blocks are homogeneous degree-two
rational functions on L_qc with only the 3m earlier simple poles.
Clearing their common product gives binary forms of degree 3m+2,
an ambient space of dimension 3m+3. Thus their stacked transverse
observation rank is at most 9m+9. The same bound also holds after
adding the special S columns: as checked below, the L_d normalization
cancels their apparent other-q-line poles. The ceiling shows why a
complementary observation is needed to distinguish all
18m regular incoming/shared columns for large m. Neither (LC50)
nor this dimension count proves the remaining source transversality.

## What the longitudinal layer already contains

The augmented coordinate theorem also determines the longitudinal
double-pole map on the actual copied-old span C. For t<=m,

\[
 C(F_{t,q,a,c})=p_{tac}e_c(I-K_qT_tK_q),
\]
\[
 [L_{qc}^2 C(F_{t,q,a,c})]_{L_{qc}=0}
 =-X_c^2v_c\left[
 A_t(a,c)\frac{X_a}{L_{ta}}\frac{(v_cT_t)_c}{X_c}\right].
 \tag{LC51}
\]

There is no squared pole on any other q-line. The actual three-column
sum sum_b C(F_(q,1,c,b)) has squared coefficient
-X_c^2 v_c (v_cQ)_c/X_c on that same line and none on the other
two. The final old kernel cancels the displayed X_c division.
These are exactly the augmented 3m+1 coordinate-c scalar functions
of the prepend theorem, up to nonzero parameter column factors.

The scalar coefficients are degree-zero rational functions with only
the 3m earlier simple poles and are regular at the own matching point.
This target has dimension 3m+1. The augmented theorem therefore proves
that C maps onto it. The three sectors have disjoint squared-pole
support, so the full longitudinal map on C has rank 3(3m+1)=9q-6,
without assuming old-source independence. In this stated coefficient
space, every longitudinal-only observation annihilating C is zero.
This does not assert that uncorrected jets with additional matching
or pair singularities already belong to this space. It shows that a
useful additional layer must couple longitudinal data to simple poles,
prefixes, or other actual source-graph information.

For precision, the normalized transverse ceiling also includes the
special local jets. For a different from b, use d=b on L_qa and d=a
on L_qb. Their exact observations are

\[
 \frac{O_a(S_{ab})}{X_a}
 =A_q(a,b)\ell_a
       [X_bv_bQ\operatorname{diag}(X)^{-1}A_q^{-1}e_b
                       -L_b(A_q^{-1})_{bb}],
\]
\[
 \frac{O_b(S_{ab})}{X_b}
 =-A_q(a,b)X_a\ell_b
                 v_bQ\operatorname{diag}(X)^{-1}A_q^{-1}e_a.
 \tag{LC52}
\]

The other state gives zero. The apparent pair pole in the unnormalized
squared coefficient is canceled by L_d. Any alternative transverse
choice gives the negative of this normalized observation by zero sum.
The final Q kernel cancels coordinate divisions. The diagonal S
formula and diagonal W formula likewise have degree two and only old
simple poles; C, off-diagonal W and Z are killed. Thus the entire
observed family O(B,J,U,V), divided by X_c in each sector, lies in the
same 9m+9-dimensional target. This corrects the earlier restriction of
that ceiling to regular U,V: the apparent extra q-line poles occur
before normalization, not in O itself. The rank bounds above are
unchanged by this scope correction.

## Full transverse rank and the exact remaining nine-q-column problem

The weighted prepend proof (SP16)--(SP22) now fills the whole transverse
target for every fixed real direction with three distinct rates. Use
the actual columns

\[
 \mathcal H=(V_{t,a,c}:t\le m,a,c)\ \cup\
              (U_{1,c,b}:c,b).
 \tag{LC53}
\]

There are 9m+9=9q such columns. After the common X_c row divisions
and polynomial clearing on each terminal line, O is a fixed
9q-dimensional binary coefficient target. O H is invertible on a
nonempty generic positive common-G/time open. This assertion uses
the actual individual shared columns, not independent surrogate
tails, and was independently audited.

Define the parameter-only projection
Pi_H(Y)=Y-H(OH)^(-1)O(Y). It kills the observed part and fixes both
C and the three E-difference jets Z, since OC=OZ=0. Under the
shorter-source independence premise, C has rank N_q and Z is
independent modulo C by the existing local matching proof. Therefore
the full leading-plus-first-jet list satisfies the exact identity

\[
 \operatorname{rank}[B,D']
 =9q+\operatorname{rank}
   [C,Z,\Pi_{\mathcal H}W,\Pi_{\mathcal H}S,
                       \Pi_{\mathcal H}U_{s\ge2}],
\]
\[
 \operatorname{rank}[B,D']\ge N_q+9q+3.
 \tag{LC54}
\]

The remaining projected columns number 9+9+9(m-1)=9q. Thus full
rank of this first-jet list is equivalent to their independence
modulo span(C,Z). This criterion does not assume the six leading
off-diagonal W columns independent, require a new ambient-membership
lemma, or ignore any correction: every projected row retains its
explicit H(OH)^(-1)O term. It combines the leading and jet gaps in
one 9q-column problem.

The lower bound gives N_q+39 at q=4 and N_q+48 at q=5. The gap to
N_(q+1)=N_q+18q+3 is exactly 9q. Nonvanishing of the remaining
quotient determinant would supply the full first-jet induction step
and hence actual source independence near the collision. It is not
proved. The equivalence here is for full first-jet rank; actual source
independence might also hold through higher jets if this first-jet
test were deficient.

## A concrete prefix target for the remaining columns

The remaining quotient in (LC54) admits the following independently
audited paper reduction. Retain the generic old geometry, the full
transverse frame (LC53), and the scalar longitudinal fullness (LC51).
In addition, at each q-line pair P_ab require both ell_a(P_ab) and
ell_b(P_ab) nonzero, and at each own matching point require
ell_c(M_c) nonzero. These are generic conditions for each fixed
direction with three distinct rates: a generic row b avoids the plane
spanned by row a and row a times D. Their nonempty opens can therefore
be intersected with the preceding common-G/time opens.

For every one of the 9q projected columns Y in (LC54),

\[
 Y\in\operatorname{im}T_q\oplus\operatorname{span}(Z_0,Z_1,Z_2).
 \tag{LC55}
\]

This is a membership statement for these actual projected source
columns, not an identification of every rational row killed by O.
Here is a constructive proof, retaining the source tangent conditions.

Every leading row or first jet is the first coefficient of a family
Y_epsilon of ambient source rows with Y_0=0. For a leading row,
multiply its actual family by epsilon; for a jet, use its actual
vanishing difference. The projection coefficients in Pi_H are
parameter constants independent of X and epsilon, so this remains
true after projection and linear combinations.

At a q-line pair, the possible total-order-three part of such a
first coefficient has the universal form

\[
 \left(\frac{\ell_a}{L_a^2L_b}
       -\frac{\ell_b}{L_aL_b^2}\right)z_{ab},
 \qquad z_{ab}\mathbf1=0,
 \tag{LC56}
\]

with all coefficients evaluated at P_ab. To see the relative sign,
the two mixed denominators in the vanishing family have opposite
constant coefficients at the collision; differentiating their moving
factors gives (LC56). A term with two visits to the same state has
no third-order single-line part, as in the diagonal cancellation
already used in (LC20). Evaluating O_a and O_b at P_ab gives,
up to their nonzero normalization factors, ell_a z_ab lambda_b and
-ell_b z_ab lambda_a. The two contractions separate the zero-sum
row plane, since v_a and v_b are independent there. Thus OY=0
forces z_ab=0 at every pair.

The remaining squared coefficient on L_c is longitudinal, h_c v_c.
The fixed matching condition gives h_c(M_c)=0. Consequently its
divided matching observation (LC19) is a scalar multiple
eta_c A_q(c,:). Subtract the unique multiple
eta_c/ell_c(M_c) of Z_c. Equation (LC21) shows that the new divided
coefficient vanishes to second order, so h_c is divisible by X_c^2
on L_c. There are no residual other-q-line poles in this squared
coefficient: those would have appeared in (LC56). What remains is
exactly the degree-zero, old-simple-pole longitudinal target of
(LC51). Its full 3m+1-dimensional scalar basis in each sector
therefore removes every squared pole by subtracting actual copied
columns C. This step requires only the scalar interpolation inverse,
not the full old-source inverse.

The row now has only simple q-line poles. At each unordered pair
a,b remove its two simple-pair residues with the two ambient rows

\[
 J_{ab}=\frac{X_aX_b}{L_a}e_b(I-K_q)
       =T_q(0,I_{ab}),\qquad
 I_{ab}=\frac{X_aX_b}{L_a}e_b.
 \tag{LC57}
\]

These are admissible prefixes. Their pair coefficients are
-X_aX_b v_b and -X_aX_b v_a, which span the zero-sum row plane.
They introduce no squared q-line pole or earlier-line pole.

It remains essential to check the divided matching condition after
these subtractions; pole cancellation alone would not suffice.
Every subtracted row still has a vanishing ambient family: for a
row in im(T_q), use epsilon T_n(R,I), and for Z use the original
vanishing source difference. Let D_old be the product of the old
row forms and D_new(epsilon) the product of the moving new ones.
For each output j its cleared divided polynomial has an expansion

\[
 p_{\varepsilon,j}
  =D_{\rm old}D_{\rm new}(\varepsilon)
                 Y_{\varepsilon,j}/X_j
  =\varepsilon p_{1,j}+\varepsilon^2p_{2,j}+\cdots.
 \tag{LC58}
\]

It vanishes both at the fixed old matching point M_c and at the
moving new matching point M_c(epsilon). Hence
p_1(M_c)=p_2(M_c)=0 and d p_1(M_c)[M_c'(0)]=0. Once the squared
pole has been removed, locally
p_1=unit times L_c times (L_c Y_j/X_j). The matching point has
nonzero normal velocity, since ell_c(M_c) is nonzero. The derivative
condition therefore gives (L_c Y_j/X_j)(M_c)=0, including the
divided output j=c condition. All other old matching, coordinate,
zero-sum and same-block conditions are inherited or were explicitly
removed above. The resulting row S belongs to W0_q.

Finally W0_q is contained in im(T_q). Apply the existence formulas
(PP3)--(PP6) with A=A_q:

\[
 k=S\operatorname{diag}(X)^{-1},\quad
 j=E(kA_q^{-1})A_q,\quad I=j\operatorname{diag}(X),
 \qquad R=I+(S-I)K_q^{-1}.
 \tag{LC59}
\]

The existence proof still gives R in W0_q and T_q(R,I)=S when
the new lines coincide with the q-lines. Its factors L_qc only
multiply the interpolated residues. The separate uniqueness proof
in PP uses new/old nonincidence and is not applied here; the exact
collision ambiguity is instead (LC2). Combining these preimages
proves membership in (LC55). Moreover Theta annihilates im(T_q):
each divided double coefficient has two incoming X_c factors.
Equation (LC21) then proves its intersection with span(Z) is zero.

Under shorter-source independence, choose any ambient preimage

\[
 Y-\sum_c z_cZ_c=T_q(R_Y,I_Y),\qquad
 \Gamma(Y)=\operatorname{ResPrefix}_{\rm old}
                   (I_{\rm old}(R_Y)-I_Y).
 \tag{LC60}
\]

The notation ResPrefix_old means the 9q coefficients of X_a/L_ta
in the three components of the prefix divided by diag(X). By
(LC2)--(LC3), a different preimage changes its defect only by a
diagonal polynomial prefix, so these coordinates are well-defined.
Their vanishing means the defect is such a polynomial prefix;
the explicit kernel generators then remove it and put Y in
span(C,Z). Conversely every row in span(C,Z) has zero coordinates.
Consequently the exact remaining criterion is

\[
 \det\left[
   \Gamma(\Pi_{\mathcal H}W),\
   \Gamma(\Pi_{\mathcal H}S),\
   \Gamma(\Pi_{\mathcal H}U_{s\ge2})
       \right]\ne0.
 \tag{LC61}
\]

This is a 9q-by-9q matrix in specified old-pole prefix coordinates.
The longitudinal subtraction uses known actual copied coefficients
and contributes zero graph defect. The remaining recovered old row
still requires its actual source prefix I_old(R_Y); replacing that
map by an arbitrary ambient interpolation would change (LC61).
The reduction proves neither this determinant's nonvanishing nor a
recurrence for it. A structural computation of that determinant,
with all projection and source-prefix corrections retained, remains
the next all-length obligation.

## Computing every defect coordinate by local extraction

The [complementary-observation investigation](https://chatgpt.com/c/6ad1a136-2ed4-83eb-877e-ce9f7f4f96fd)
proposed an explicit earlier-line extraction. Local derivation and
independent audit identify it with the negative of (LC60). A further
local calculation below recovers the terminal nine coordinates as well.
Thus the full old-source inverse in the abstract definition can be
replaced by the old F cross-pair residue inverse followed by scalar
line evaluations. This remains a conditional construction under
shorter-source independence, not a determinant nonvanishing proof.

Let D stack two components of every cross-block old double residue,
with fixed projective representatives, and put

\[
 \mathscr D_q=[D(F_{tsab})]_{t\ne s,a,b},\qquad
 T_K=A_q^{-1}\operatorname{diag}(L_q)-\operatorname{diag}(X).
 \tag{LC62}
\]

There are 9q(q-1) rows and columns in script D_q. This matrix is
invertible under the old-source premise. Indeed the kernel of D on
W0_q is exactly the old E span: after the cross-pair residues vanish,
each line residue is a quadratic polynomial row. Coordinate factors
and the divided matching condition make its j-component a constant
times X_a X_j. Zero sum on L_ta=0 makes that constant vector a
multiple of A_t(a,:), so an E_ta removes the residue. The remaining
polynomial row has degree one, output-coordinate factors and zero
sum, hence is zero. The actual old E/F basis then makes the F block
square and nonsingular.

For a residual Y in (LC55), remove its unique zZ part using Theta
and (LC21), and write Y0=Y-sum z_c Z_c. Multiplication by
K^-1=diag(X)^-1 A^-1 diag(L) leaves only simple terminal poles:
the off-state squared coefficients are exactly O, and the own-state
factor L_c removes one pole. The actual collision pole restrictions
and OY=0 are essential here. Coordinate factors remove the apparent
axis divisions. Define

\[
 \alpha=\mathscr D_q^{-1}D(Y_0K^{-1}),\qquad
 \widehat Y=Y_0-\sum_{t\ne s,a,b}\alpha_{tsab}C(F_{tsab}).
 \tag{LC63}
\]

The same alpha can be computed from Y because Z K^-1 has only
terminal poles. The exact copied identity is

\[
 C(F_{tsab})K^{-1}
   =F_{tsab}+\frac{X_a}{L_{ta}}A_t(a,b)e_bT_K.
 \tag{LC64}
\]

Its second term has only a single old denominator. Therefore
D(Yhat K^-1)=0. By (LC55), any ambient preimage of Yhat has old
row in the kernel of D, hence an E combination. This is the only
source inverse used below; the F coefficients alpha remain actual
source coefficients throughout.

For an earlier line i=(t,a), t<=m, set
w_i=(L_i Yhat K^-1/X_a)|_{L_i=0}. All cross-pair residues have
been removed, same-earlier-block residues were absent, and the
inherited divided matching condition supplies the X_a factor.
Thus w_i is a homogeneous linear zero-sum polynomial row on the
line. Put P_ij={L_i=X_j=0}, and recover

\[
 h_i=\left(\frac{w_{i,j}(P_{ij})}{L_{qj}(P_{ij})}\right)_{j=0}^2 A_q,
 \qquad w_i=h_iT_K-\lambda_i v_i,
 \qquad G_i=h_i+\lambda_i A_t(a,:).
 \tag{LC65}
\]

All denominators L_qj(P_ij) are units by generic earlier/terminal
nonincidence. At j=a, the definition requires exact division by X_a
before evaluation; the undivided matching value would lose data.
The first formula makes every component of w_i-h_iT_K vanish at
its coordinate-edge point. Each is therefore a multiple of X_j;
zero sum on L_i makes the coefficient vector proportional to A_i.
This proves the second formula and uniqueness of lambda_i. It can
be read from any component after division by its nonzero A_i,j X_j.

These three numbers G_i equal minus the three earlier-line
coordinates of Gamma(Y). To check the sign directly, let the old
E coefficient of an ambient preimage be lambda_i and its prefix
pole coefficient be h_i. Then the actual E prefix is E_i, whose
pole coefficient is -A_i, so I_old(R)-I has coefficient
-lambda_i A_i-h_i=-G_i.

There is a useful equivalent correction formula. Define G_tail
by applying this extraction to Y0 K^-1-sum alpha F, subtracting
ordinary old F after transport. Subtracting the actual copied
columns instead gives

\[
 G_i^{\rm actual}=G_i^{\rm tail}
              -\sum_{s\ne t,b}\alpha_{tsab}A_t(a,b)e_b.
 \tag{LC66}
\]

The subtraction changes h_i by the displayed row and leaves
lambda_i unchanged. These are the actual grouped source-prefix
margins. A tail-only calculation that omits them computes a
different matrix.

For g a constant row define the admissible ambient representative
N_i(g)=(X_a/L_i)g diag(X)(I-K)=T_q(0,(X_a/L_i)g diag(X)).
Remove all earlier poles by setting

\[
 R_0=\widehat Y-\sum_{t\le m,a}
                   \{\lambda_i E_i+N_i(G_i)\}.
 \tag{LC67}
\]

After right multiplication by K^-1, the residue of the subtracted
row, divided by X_a, is
-lambda_i A_i A^-1 diag(L)+G_i T_K
=h_i T_K-lambda_i v_i. Thus (LC67) has only terminal q-line
poles and belongs to im(T_q). Neither E_i nor N_i(g) introduces
a cross-block double residue after right transport. The E terms
have zero graph defect; N_i(G_i) has defect -G_i at precisely its
own prefix line.

The terminal-only space in im(T_q) has the explicit basis

\[
 \{E_{qa}:a=0,1,2\}\ \cup\
 \{N_{qa}(e_b):a,b=0,1,2\}.
 \tag{LC68}
\]

For spanning, the old row of an ambient preimage has zero
cross-pair residues and is E-only. Absence of earlier poles and
the injectivity of (LC65) force all earlier E and prefix
coefficients to vanish. The preimage therefore has only terminal
E rows, terminal prefix poles and a diagonal polynomial prefix.
The last part times (I-K) is an E_q combination. Rewriting
T_q(R,I)=R+(I-R)(I-K) proves spanning by (LC68).

The following local inverse proves independence and supplies its
nine quotient coordinates modulo E_q. For each terminal line let
w_a=(L_a R_0 K^-1/X_a)|_{L_a=0}. If the terminal old row has
coefficient lambda_a and the terminal prefix pole has row h_a,
then

\[
 w_a=h_aT_K-\lambda_av_a=G_aT_K,
 \qquad G_a=h_a+\lambda_aA_q(a,:),
 \tag{LC69}
\]

because A_q(a,:)T_K=L_a e_a-v_a. In particular w_a is a linear
polynomial row. For j different from a, take P_aj={L_a=X_j=0}
and set g_j=w_a,j(P_aj)/L_j(P_aj). These two ratios are
(G_a A^-1)_j. The own component on the entire line gives the
constant delta_a=-w_a,a/X_a=G_a,a. Complete the three-variable
solve by

\[
 g_a=\frac{\delta_a-\sum_{j\ne a}g_jA_q(j,a)}{A_q(a,a)},
 \qquad G_a=gA_q.
 \tag{LC70}
\]

The coefficient A_q(a,a) is nonzero. The exact quotient defining
delta_a can be evaluated at any point of L_a with X_a nonzero;
it is not an assumed value at the matching point. This inverse
recovers all nine terminal prefix-defect coordinates with the
same minus sign as (LC65). It also proves the nine N_q classes
independent modulo the three E_q rows, so (LC68) has dimension
twelve. The three E_q rows themselves are independent by their
distinct line residues.
For a fixed ordering d,e of the other two states, the linear map
G_a to ((G_a A^-1)_d,(G_a A^-1)_e,G_a,a) has determinant
plus or minus A_q(a,a)/det(A_q). Thus the three terminal solves
together contribute the explicit nonzero factor
plus or minus A_00 A_11 A_22/(det A)^3.

Stack (LC65) for all earlier lines and (LC70) for the terminal
lines. The resulting 9q-vector is exactly -Gamma(Y), including
every projection correction and source margin. Consequently
(LC61) can be computed using script D_q inverse and these local
linear solves, without evaluating the full map I_old on arbitrary
recovered rows or invoking the PP interpolation inverse. This
does not remove the old-source dependence: it is retained in the
actual F residue matrix and its inverse. No prepend recurrence or
uniform nonzero determinant coefficient has yet been proved.

## Exact finite check of the specified transverse projection

The [projection script](../exploration/source24_collision_projection.py)
and [saved certificate](../exploration/source24-collision-projection-results.json)
check the exact frame and projection in (LC53)--(LC54) at the existing
q=4, relative-direction (1,2), p=1000003 fixture. They reuse the saved
actual ordinary source evaluations and independently extract the
terminal Laurent observations from the actual ordered words.

| Matrix | Size or rank | Determinant modulo 1000003 |
|---|---:|---:|
| O(H) | 36 by 36 | 508580 |
| Selected ordinary C,Z minor | 123 by 123 | 164520 |
| Corrected quotient minor | 36 by 36 | 339987 |
| Combined observation/evaluation minor | 195 by 195 | 945187 |

The last determinant is the product of the first three after the
recorded parameter-only column corrections. All 24,570 single-line
cubic coefficients cancel before contraction by the fixed covectors.
The extracted observations agree with 8,190 independently derived
LC formula entries. Twelve nodes per terminal line determine its
degree-eleven cleared observation polynomial; two extra nodes check
1,170 further values. A further 1,170 actual dual-number entries
reconstruct the saved ordinary values. Coordinate and denominator
units, O(C)=O(Z)=0, and both projection identities are checked.

The certificate records the full observation matrix, all correction
coefficients, row and column labels, hashes, and the quotient minor.
One bounded run took 5.24 seconds externally with peak RSS 41,009,152
bytes; both the primary and an independent reviewer audited the code
without rerunning it. This verifies the specified new projection at
one fixture. The determinant 339987 belongs to a sampled quotient
coordinate matrix, not the canonical graph-coordinate matrix (LC61).
The two tests have the same rank under the proved identification,
but their determinants need not coincide. This is external exact
finite evidence, not a Lean result or an all-q nonvanishing theorem.

## A direct block matrix with sparse source-margin rows

The local extraction can also be performed before subtracting the F
columns. This gives an explicit Schur form with a fixed actual-source
correction matrix. For i=(t,a), define on the old ambient space

\[
 e_i(R)=-\frac1{A_t(a,a)}
       \left[\frac{L_iR_a}{X_a^2}\right]_{L_i=0}(M_i).
 \tag{LC71}
\]

The quotient is canceled on the line before matching evaluation.
The ambient coordinate and matching conditions make it regular, and
e_i(E_j)=delta_ij. For Y0=Y-sum zZ=T_q(R,I), let h_i be the pole
coefficient of I diag(X)^-1 at X_a/L_i and set

\[
 G_i(Y_0)=h_i+A_t(a,:)e_i(R).
 \tag{LC72}
\]

This is independent of the collision preimage ambiguity: at a terminal
kernel generator, the changes h_i=A_q(a,:) and e_i(R)=-1 cancel.
It is a direct local observation of Y0, without computing R or I.
Indeed u_i=(L_iY0 K^-1/X_a)|_{L_i=0} has the form
Res_i(R)/X_a+h_iT_K. Its first summand's j-component vanishes at
P_ij, including j=a by divided matching. On earlier lines the
three coordinate-edge values therefore recover h_i exactly as in
(LC65), and

\[
 e_i(R)=-\frac1{A_t(a,a)}
       \left[\frac{(u_i-h_iT_K)_a}{X_a}\right](M_i).
 \tag{LC73}
\]

Here u_i is generally rational on the line, with cross-pair poles;
no polynomial or constant-on-the-line assertion is made. All
evaluation points avoid those poles. At terminal line a, the two
other coordinate-edge values give (G_a A^-1)_j, j different from a,
as before. The third datum is now
delta_a=-[u_a,a/X_a](M_a), evaluated after cancellation at matching.
It equals G_a,a. Formula (LC70) then recovers G_a. Before the earlier
and F subtractions, this canceled ratio need not be constant along
the line. This distinction is necessary for the direct construction.

For an actual old F column define the three-entry block

\[
 M_{i,F_{tsab}}=
 \mathbf1_{i=(t,a)}A_t(a,b)e_b+A_i e_i(F_{tsab}),
 \qquad B(Y_0)=D(Y_0K^{-1}).
 \tag{LC74}
\]

All entries are explicit old-source residues or matching values.
With alpha=script D_q inverse B, the old row decomposes as
R=sum alpha F+sum_i lambda_i E_i, where
lambda_i=e_i(R)-sum_F alpha_F e_i(F). Applying the actual source
prefix conventions gives exactly

\[
 \Gamma(Y)=-G(Y_0)+M\mathscr D_q^{-1}B(Y_0).
 \tag{LC75}
\]

Equivalently M=G(C(F)) and G(C(E))=0. Thus the residual square
matrix is a Schur complement of the completely specified block
matrix

\[
 \begin{pmatrix}
    \mathscr D_q&B(\mathcal Y_0)\\
    M&G(\mathcal Y_0)
   \end{pmatrix},
 \quad
 \mathcal Y=(\Pi_H W,\Pi_H S,\Pi_H U_{s\ge2}).
 \tag{LC76}
\]

Its determinant is (-1)^(9q) det(script D_q) det(Gamma(mathcal Y)).
This gives an explicit matrix identity, not a proof of either new
determinant's nonvanishing.

In each three-row block, quotient by span(A_i). The matching part
of (LC74) disappears, leaving only the shared-head source margins
indicator_{i=(t,a)} A_t(a,b)e_b. A parameter-only invertible row
change therefore splits the target into 6q sparse margin coordinates
and 3q remaining coordinates that retain the matching terms. The
split is exact; it provides no rank conclusion by itself. The direct
observation, source signs, and Schur identity were independently
audited.

Two concrete issues remain for a preserving-prepend recurrence.
First, diag(r)+11^T, even after row and column scaling, lies on
the hypersurface G_01 G_12 G_20=G_02 G_21 G_10. Generic old-source
independence on unrestricted G does not imply old script D_q is
invertible throughout, or generically within, that specialization.
A separate restricted-family theorem or a controlled transverse
perturbation of G is required. Second, for an actual old source
whose completed word starts P_s=K_s R_s, insertion of a new
earliest block Kcirc gives P_s^+=K_s Kcirc R_s and

\[
 F_{tsab}^{+}=F_{tsab}
             +p_{tab}e_bK_s(I-K^{\circ})R_s.
 \tag{LC77}
\]

The first-slot-dependent factor K_s remains. The scalar preservation
identity v Kcirc=S v used for the transverse theorem does not
remove this actual source correction. A useful next lemma must
control script D_q and M jointly under (LC77), including the
matching coordinates and all source margins. Neither the old
independence premise nor full transverse rank supplies that lemma.

The restricted-family issue has exact finite bases. The
[weighted source script](../exploration/source24_weighted_source_base.py)
and [saved certificate](../exploration/source24-weighted-source-base-results.json)
use r=(2,3,5), Gtilde=[[3,1,1],[1,4,1],[1,1,6]], first-column
row normalization, and times (8^t,8^(2t)). At p=1000003 the actual
F cross-pair matrices have rank 54 and determinant 70515 at q=3,
and rank 108 and determinant 866635 at q=4. These determinants
use the ordered pair basis (v_uc,v_vd) for each vector residue,
rather than its first two output components. The full ranks give
finite source bases by the already proved E-kernel characterization.

Strong geometry checks include same-block pairs and coordinate-edge
incidences. An independent polynomial-cleared numerator verifies all
three residue components, retaining the actual source factor and
word order; separate ordinary evaluations check that factor again.
The fixed fixture was neither replaced nor scanned. One run took
0.23 seconds externally with peak RSS 18,874,368 bytes. The primary
and an independent reviewer audited the script without rerunning it.
These prove nonempty generic rank opens within the preserving family
at q=3 and q=4 only. The restricted-family rank theorem for arbitrary
q and the recurrence for the residual matrix remain open.

## The entire flat collision ambient has the direct-sum decomposition

The [flat-collision investigation](https://chatgpt.com/c/6ad1a73b-3900-83eb-89a3-f5d3a9828d96)
supplies a second, shorter membership proof. Its saturated-lattice
argument was independently audited locally. It proves a stronger
ambient statement than (LC55), and does not need that proof's extra
pair-motion conditions or the longitudinal fullness (LC51).

For generic k-block geometry, an ambient basis consists of E_i and,
for every unordered cross-block pair i=(t,a), j=(s,b), the two rows
h_j E_i and h_i E_j, where h_i=X_a/L_i. At the pair their double
residues are -X_a X_b v_i and -X_a X_b v_j. They are independent
zero-sum rows and affect no other double residue. After removing
all these pairs, the same divided matching argument as in (LC62)
leaves precisely the E span. Consequently this geometric basis
has dimension N_k, without using actual source independence.

Work over the field F of old parameters and use the formal
common-G deformation A_n(epsilon)=A_q diag(1,1+tau epsilon,
1+nu epsilon). Clear the divided output rows by the product
D_epsilon of all old and new row forms. This embeds the generic
(q+1)-block ambient into a fixed finite-dimensional homogeneous
polynomial space V over F((epsilon)). Let

\[
 \mathcal L=W_\varepsilon^{\rm cleared}\cap V[[\varepsilon]],
 \qquad
 \mathcal A_0=
   D_0^{-1}(\mathcal L/\varepsilon\mathcal L)
                 \operatorname{diag}(X).
 \tag{LC78}
\]

The power-series intersection is a finitely generated torsion-free
module over the discrete valuation ring F[[epsilon]]. It is free
of rank N_(q+1). Saturation gives
L intersect epsilon V[[epsilon]]=epsilon L, so its reduction
injects into V. Since D_0 is a nonzero polynomial even though
its terminal factors repeat, the displayed rational-row map is
injective and dim A0=N_(q+1). This is the saturated flat limit,
not the solution space of naively specialized ambient equations.

All actual leading columns belong to A0. Every stated first jet
also belongs: clear its actual vanishing source difference and
divide by epsilon, whose constant coefficient is zero before the
division. The resulting power-series lattice element reduces to
D_0 times that divided jet.

Every ambient append image also lifts. If R=r diag(X) is in W0_q
and I=j diag(X) is a prefix, the divided row of T_n(R,I) is

\[
 j+(r-j)\operatorname{diag}(X_a/L_{na})A_n.
 \tag{LC79}
\]

It preserves old matching and same-block conditions. Its new-line
residue has an explicit X_a factor, giving the new matching
condition, and a single new kernel introduces no same-new-block
double residue. Coordinate factors and zero sum are preserved.
Thus T_n(R,I) belongs to the generic new ambient and has a regular
cleared limit, proving im(T_q) is contained in A0. By (LC2) its
dimension is N_q+9q. The three Z directions also lie in A0 and
are independent modulo im(T_q) by their divided matching
observations (LC19)--(LC21).

Finally the actual frame H in (LC53) lies in A0 and has 9q
independent O images, while O kills im(T_q) and Z. Therefore
their direct sum has dimension
(N_q+9q)+3+9q=N_(q+1), the whole flat ambient:

\[
 \mathcal A_0=
   \operatorname{span}\mathcal H
        \oplus\operatorname{im}T_q
        \oplus\operatorname{span}Z,
 \qquad
 \ker(O|_{\mathcal A_0})=
        \operatorname{im}T_q\oplus\operatorname{span}Z.
 \tag{LC80}
\]

No old-source independence is used in this ambient decomposition.
It uses generic geometry, the ambient kernel calculation, and the
proved full transverse frame. O may initially be regarded as taking
values in all rational line observations; the dimension argument
then forces its image to equal O(H). Thus it does not presuppose
that every flat-limit row has the bounded binary-form observations.
Alternatively the fixed 9q line evaluations witnessing O(H) give
the same direct-sum argument.

This proves membership for every actual residual in (LC54) with
fewer auxiliary hypotheses and identifies the entire flat ambient.
It does not identify the actual source span with that ambient.
Under shorter-source independence the exact source rank is still
N_q+9q+3+rank(Gamma(mathcal Y)), and the remaining determinant
(LC61), equivalently (LC76), is still unproved for arbitrary q.

## Explicit new matching rows under a weighted prepend

There is an audited recurrence for the M side of the joint block
problem. Use the unnormalized Gtilde=diag(r)+11^T, r_a>0, and
prepend a block denoted circle with time vector (1,1,1). Its own
matching point Q_a has X_a=0, X_i=1, X_j=-1 for the other two
states i,j. Assume all old row forms are nonzero there and all
time factors are nonzero. Write b_t=(1,u_t,v_t), and let d_t be
the determinant of the active two-state restriction of K_t at Q_a.
Set theta_t=[(e_i-e_j)K_t e_a/X_a](Q_a), after cancellation.
With C_a=r_i+r_j+r_i r_j, direct two-by-two calculation gives

\[
 d_t=-\frac{C_a b_{ti}b_{tj}}{L_{ti}(Q_a)L_{tj}(Q_a)},\qquad
 \frac{\theta_t}{d_t}
   =\frac{b_{ta}}{C_a}
          \left(\frac{r_i}{b_{tj}}+\frac{r_j}{b_{ti}}\right).
 \tag{LC81}
\]

Put Delta=product_t d_t. For a retained old-head source
F^+_(t,s,c,b), q>=3, let ell=max(old blocks minus {t,s}). Then

\[
 e_{\circ a}(F^+_{t,s,c,b})
 =\frac{\Delta}{A_\circ(a,a)}
    \frac{p_{tcb}(Q_a)}{d_t}
    \frac{b_{sa}}{L_{sb}(Q_a)d_s}
    \frac{\theta_\ell}{d_\ell},\qquad c,b\ne a.
 \tag{LC82}
\]

If c=a or b=a this matching value is zero. The formula retains
the actual inserted word K_s Kcircle R_s from (LC77). Indeed its
new-line residue is -p_tcb (K_s)_ba v_circle,a R_s. Divide by
X_a twice before matching: entry into a contributes b_sa/L_sb,
and v_circle,a(Q_a)=e_i-e_j propagates through the nonempty
binary zero-sum suffix. Every factor before its last block
contributes d_t; the last contributes theta_ell. The definition
of e in (LC71) cancels the residue's minus sign. If c or b equals
a there is one additional X_a, yielding zero. The nonempty suffix
is why this statement requires q>=3.

For fixed active c,b the off-diagonal time-pair table in (LC82)
has the form f_t g_s h_max(old minus {t,s}), up to the common
factor. It admits a rank-at-most-three completion: away from row
and column q it is h_q f g^T, and every change is supported in
row q or column q. The exceptional pair {q-1,q} uses h_(q-2).
Thus this matching row is controlled by separable time aggregates
and explicit terminal row/column corrections, not arbitrary
completed-word coefficients.

For the sum over all nine new-head columns grouped by a and a
fixed first slot s, the three-column sum satisfies

\[
 M_{\circ a}\left(\sum_bF_{\circ,s,a,b}\right)
 =A_\circ(a,:)
      \frac{\Delta}{A_\circ(a,a)}\frac{\theta_\ell}{d_\ell},
 \quad
 \ell=\begin{cases}q&s\ne q,\\q-1&s=q.\end{cases}
 \tag{LC83}
\]

Its matching functional equals -1 plus the scalar on the right;
the actual head margin cancels that -1. Omitting either term
would give the wrong recurrence.

The six new quotient-margin rows can be made especially explicit.
For each a use x_j/A_circle(a,j)-x_a/A_circle(a,a), j different
from a, on its three-entry M block. These rows vanish on every
retained old-head column. On the six new-head columns with b
different from a at any fixed first slot, they form I_6. Replacing
the remaining three diagonal columns by the three sums over b
makes those columns zero in these six rows. These are exact pivots
in the augmented (D,M) data. They do not prove six new D pivots
or a source-rank gain. The three new matching rows and the actual
inserted-word correction to D remain coupled. Equations
(LC81)--(LC83) compute the matching half of that next problem;
they do not complete its determinant recurrence.

## Time normalization and two further weighted finite bases

The global time-scaling identity proposed by
[Pro40](https://chatgpt.com/c/6ad1abf4-9d9c-83eb-a330-66a5d8ae19f5)
has a direct proof for every fixed length and every common matrix.
Let H=diag(1,h_1,h_2), with both h_j nonzero, and delta=h_1 h_2.
Replace every time vector (1,u_t,v_t) by (1,h_1 u_t,h_2 v_t).
Then Ahat_t=A_t H, Khat_t(Y)=K_t(HY), and each canonical
cross-product node transforms by Phat=delta H^(-1)P. At that node
every regular kernel is unchanged, each pole-residue kernel gains
a factor delta, and the head coordinate P_a gains delta/h_a.
Consequently, with identical row and column orderings,

\[
 \widehat{\mathscr D}_{\rm raw}
   =\mathscr D_{\rm raw}
       \operatorname{diag}_{(t,s,a,b)}(\delta^3/h_a),\qquad
 \widehat{\mathscr D}_{\rm pair}
   =\mathscr D_{\rm pair}
       \operatorname{diag}_{(t,s,a,b)}(\delta^2/h_a).
 \tag{LC84}
\]

Here raw means the first two output components of the actual
double residue. Pair means the coefficients in (v_i(P),v_j(P)),
the convention of (LC62). The latter basis vectors each gain
delta, accounting for the different factors. Thus the determinant
exponents are respectively 24q(q-1) and 15q(q-1). These formulas
retain the literal ordered word. They use the exact cross-product
representatives; arbitrary projective renormalization changes the
displayed diagonal factors.

Any designated time can therefore be fixed to any nonzero target
without changing source rank or the common G. Positive targets
preserve positivity. For the unnormalized weighted family, setting
a designated time to (r_0+1,r_0+1) makes its normalized row 0
equal (1,1,1). This transports fixed-length witnesses; it does not
prove independence on the entire weighted family or at a new length.

The local checker `source24_weighted_extended_base.py` independently
reproduces the two additional Pro40 finite cases q=5,6, using
r=(2,3,5) and the initial segments of the single time list
(2,3),(5,7),(11,13),(17,29),(31,47),(53,73). Modulo 1000003,
the normalized pair-coordinate matrices have full ranks 180 and
270, with determinants 440800 and 760635. Separately assembling
the unnormalized tables and taking the first two output components
reproduces the external determinants 226299 and 160943 exactly.

The saved JSON includes the actual matrices, ordered columns,
geometry checks, pivot certificates, and independent polynomial
clearing of all three output components. It also checks the
row-normalization change between both residue constructions.
The single run took 3.00 seconds and peak RSS 36,601,856 bytes.
These are external exact finite certificates, not Lean theorems.
Together with the earlier q=3,4 cases, they establish finite bases
inside the weighted family at four lengths. The all-length
determinant recurrence remains open.

## An all-length boundary family invisible to the new matching rows

There is a local Newton-style induction for actual new-head sums.
It proves a growing rank before the quotient by retained old columns.
Keep the weighted prepend and write
P_s=K_s product_(j in old minus s, increasing) K_j. For q>=2 set

\[
 Z_{a,s}=\sum_b(F_{\circ,s,a,b}-F_{\circ,1,a,b}),
 \quad 2\le s\le q,\qquad
 v=A_\circ(a,:)\operatorname{diag}X.
 \tag{LC85}
\]

The residue of Z_(a,s) on its own new line is
X_a v(P_1-P_s); it has no other new-line pole. On that line put
A_s^(q)=v(P_1-P_s). For s<q these rows equal A_s^(q-1)K_q.
Right multiplication by the rational inverse K_q^(-1) preserves
linear independence over the parameter field, with coefficients
constant in X. It returns the inherited rows to A_s^(q-1), while
the new row s=q becomes

\[
 vP_{\rm old}-vK_qP_{\rm old}K_q^{-1},\qquad
 \mathop{\rm Res}_{L_{qd}=0}
   =-v_d\,v_{qd}P_{\rm old}K_q^{-1}.
 \tag{LC86}
\]

The inverse is regular at this pole when the coordinates are
nonzero: its rational formula is diag(X)^(-1) A_q^(-1)diag(L_q).
The inherited rows have no q-block pole. The displayed new residue
is generically nonzero within the common weighted family, as the
following explicit coefficient witnesses at every length.

For a=0, r=(2,3,5), take X=(1,1,-4), circle time (1,1), and
the last old time (2,1/8), with d=2. Then v=(3,1,-4),
v_q2=(1,2,-3), and L_circle,0=L_q2=0. Let all earlier times
approach (1,5/4); their row-1 pole residue is
R=e_1 v_* with v_*=(1,4,-5). The highest simultaneous coefficient
in their separate row-1 poles satisfies

\[
 v_{q2}R^{q-1}=2\,4^{q-2}v_*,\qquad
 v_*K_q^{-1}(X)=\frac{153}{122}(-1,1,0)\ne0.
 \tag{LC87}
\]

Here K_q^(-1)(X) means the regular value of the rational inverse,
which has rank two; K_q itself has a pole there. This boundary
calculation proves a coefficient is nonzero, rather than treating
the coincident-line boundary as an admissible geometric fixture.
Positive perturbations separate the old lines and retain the
nonzero coefficient. Intersecting this nonempty generic open with
the shorter independence open proves the induction, including
the q=2 base. State permutations give the same nonzero-polynomial
claim for each sector. Their finite intersection proves the joint
statement for generic positive variable r; this argument does not
claim all sectors at one fixed ordered r=(2,3,5).

Double-pole extraction is injective on these line rows. If all
their old-pole residues vanish, their combination is a homogeneous
linear polynomial row on the new projective line. Its j-th
component vanishes at X_j=0, since each completed word ends in
a kernel with that coordinate factor and the old denominators
are units at the coordinate-edge points. Thus that component is
c_j X_j. Zero row sum implies c is a multiple of A_circle(a,:),
so the row is lambda v. At the own matching point X_a=0,
every ordered old product acts on the active binary zero-sum row
by the same product of binary determinants. Every A_s vanishes
there, hence lambda=0. The factor X_a is a unit at every generic
new/old cross point, so it does not change this conclusion for
the actual residue of Z_(a,s).

Consequently D_new has rank 3(q-1) on the columns (LC85): the
three sectors have disjoint new-line support. By (LC83), their
new M map vanishes for s<q. Only s=q contributes, through
Delta/A_circle(a,a) times
(theta_(q-1)/d_(q-1)-theta_q/d_q), a generically nonzero scalar
in each sector. The M rank is therefore exactly three, and the
explicit 3(q-2) columns with 2<=s<=q-1 retain full D_new rank
inside its kernel.

This supplies an all-length obstruction to recovering D_new from
M_new, already within actual new-head source combinations. It
does not prove a new source-rank contribution after quotienting
the retained old-head columns. Controlling that intersection is
the next joint-elimination problem.

## Full new-head double-residue rank

The preceding induction extends to all 9q individual new-head
columns, without matching observations. For a fixed new line set

\[
 B_{s,b}^{(q)}=A_\circ(a,b)X_b e_b(I-P_s),
 \qquad 1\le s\le q,\quad b=0,1,2.
 \tag{LC88}
\]

These are the own-line residues of F_circle,s,a,b divided by X_a.
The induction invariant is independence of their old-pole
residues. For s<q, right multiplication by K_q^(-1) gives

\[
 B_{s,b}^{(q)}K_q^{-1}
  =B_{s,b}^{(q-1)}
    +A_\circ(a,b)X_b e_b(K_q^{-1}-I).
 \tag{LC89}
\]

The added row is polynomial, since
X_b e_b K_q^(-1)=e_b A_q^(-1)diag(L_q).
At the new old-block pole L_qd=0, only b=d among the newest
three columns has a residue after this multiplication, namely
-A_circle(a,d)X_d v_qd P_old K_q^(-1).
For unequal states a,d, (LC87) proves it is generically nonzero.
For equal states use a=d=0, the same r and point, but last old
time (5,2). Then L_q0=0, the other row forms are 13 and -42,
and v_q0=(3,5,-8). The earlier degeneration gives
v_q0 R^(q-1)=5*4^(q-2)v_*, and v_* is not proportional to
v_q0. The regular inverse has left kernel exactly span(v_q0),
so the residue is nonzero. Permutations, with harmless
normalization of the permuted time vector's first component,
cover every equal and unequal pair. As above, the simultaneous
generic conclusion allows r to vary.

Suppose a relation has zero residues at all old/new cross points.
Its row remains regular at those points after multiplication by
K_q^(-1), because every coordinate is a unit there. At the three
q-block poles, the displayed isolated residues force each of the
three newest coefficients to vanish. The remaining residues in
(LC89) are the shorter relation's residues, since the correction
is polynomial. Induction finishes the proof. For q=1, start
directly with the three disjoint poles of B_(1,b), whose residues
are -A_circle(a,b)X_b v_1b; no inverse multiplication is needed
at this base step.

Thus the actual new-head columns have full D_new rank 3q in
each new-line sector, or 9q altogether, for generic positive
parameters in the weighted family. No old-source independence
premise, matching observation, or ambient dimension argument is
used. This is a paper theorem, not yet formalized in Lean.

The remaining boundary columns F_(t,circle,c,a) cannot simply be
added as a second pivot at each pole after multiplying by
K_q^(-1). At L_qd=0, that inverse has zero column d and preserves
row sum; it maps the two-dimensional zero-sum space to a line.
The new-head and new-first candidate residues therefore become
collinear. Their joint rank needs another argument. A single
exact extraction from the saved q=4 weighted finite matrix gives
rank 54 and determinant 482791 modulo 1000003 for the entire
54-square boundary block: rows with a block-0 pole, columns
with t=0 or s=0, in their saved order. This finite check supports
the boundary-block question but does not prove it for every q.
Even its full rank would leave the retained-old-column Schur
complement to be proved nonzero.

This extraction is now saved reproducibly in
source24_boundary_block.py and its results JSON. The three
18-square sector determinants are 252004, 795650, and 365879,
with new-head rank nine in every sector. Eliminating all 27
heads gives a 27-square new-first Schur determinant 779960;
the selected head minor is 343818. Both permutation signs
are +1 and their product is 482791. The checker verifies 1,944
off-sector zeros and 27 separate two-block paired-pole formula
controls. It uses the saved, previously polynomial-checked
matrix without regenerating it. One run took 1.46 seconds,
peak RSS 17,170,432 bytes. This 27-square finite Schur matrix
is not the three-by-three recursive matrix introduced below.

## The scalar prepend leaves an explicit graph-pair obstruction

An independently audited calculation from
[Pro39](https://chatgpt.com/c/6ad1aace-81f8-83ed-b7be-25f2d7f32022)
identifies a different obstruction to a boundary-only repair of
the collision recurrence. Use Gtilde=diag(r)+11^T, w_i=1/r_i,
sigma=1+sum_i w_i, kappa=sigma-1, and ell=sum_i X_i. The new
prepend J has time (1,1), while the terminal K has time (c,c),
c=r_0+1. Then e_0 K=X/ell, and the full-plane identity is

\[
 (X+\ell w)J=\sigma X,\qquad
 e_0KJ=\sigma e_0K-wJ,\qquad
 W^+_{a0}=\sigma W_{a0}+N_a,
 \quad N_a=p_{qa0}(wJQ-\kappa e_0).
 \tag{LC90}
\]

The first equality follows from X_i+ell w_i=w_i L_circle,i;
the remaining equalities retain the actual earlier word Q.
Each N_a has only simple terminal poles, so O(N_a)=0. It cannot
be discarded merely because the scalar transverse recurrence
does not see it.

Consider the eighteen boundary source-row/prefix pairs
(p_qab e_b(I-JQ),p_qab e_b) and
(p_circle,ab e_b(I-KQ),p_circle,ab e_b).
The three pairs (-N_a,kappa p_qa0 e_0) are independent modulo
their span. Apply (R,I) -> I-R and right multiply by Q^(-1).
It suffices to prove independence of B_a=p_qa0 wJ modulo
span{p_qab e_b J,p_circle,ab e_b K}.

At ell=L_circle,i=0, i=1 or 2, take X_0=1, X_i=0, X_j=-1.
The B_0 double residue is w_i X, while all the eighteen
comparison terms have zero double residue because their
numerators contain X_i. The other two B_a have no ell pole.
Thus the B_0 coefficient vanishes in any putative relation.
For a=1,2, take its terminal-line residue, divide by X_a,
and right multiply by J^(-1). The relation becomes

\[
 \gamma_a A_q(a,0)X_0w
  =\sum_b c_b A_q(a,b)X_b e_b+f_a(X)g_a(X),
 \quad f_a=\sum_i d_i X_i\widetilde G(i,a)/L_{\circ i},
 \quad g_a=A_q(a,:)\widetilde G^{-1}\operatorname{diag}(L_\circ).
 \tag{LC91}
\]

The relevant row of A_q Gtilde^(-1) is
c e_a-e_0+w/sigma, with all three entries nonzero. Hence g_a
has no projective zero. The three circle-line intersections on
L_qa are distinct generically and have X_i nonzero there for
positive r. Their residues force every d_i=0. Then component
b different from 0 compares independent linear forms X_0 and
X_b on L_qa and forces gamma_a=0. This proves exactly the
three-dimensional quotient statement for those graph pairs.

The B_0 residue also survives the actual earlier word. At the
displayed point let z_t be the time factor for the active state
j different from 0. The binary zero-sum multiplier is

\[
 \beta_{t,i}=
 \frac{z_t[1-(r_0+1)(r_j+1)]}
 {(r_0+1-z_t)[1-(r_j+1)z_t]},\qquad
 [\ell L_{\circ i}N_0]_{X_0=1,\ X_i=0,\ X_j=-1}
     =w_i\Bigl(\prod_t\beta_{t,i}\Bigr)X\ne0.
 \tag{LC92}
\]

In the last formula X means X_0=1, X_i=0, X_j=-1, as above.
The numerator factors are nonzero for positive parameters and
the denominators are nonzero for generic earlier times. This is
an all-length nonzero coefficient of the prepend error, not of
the remaining source determinant. The graph-pair quotient here
uses only the eighteen terminal/prepend boundary pairs. It does
not include all interior-source prefix corrections or establish
a gain after the full Gamma quotient. Those corrections must
still be controlled jointly with the old-column elimination.

## A conditional three-by-three recurrence for the paired boundary block

Fix one new-line sector a. Remove the harmless constant
A_circle(a,b) from each new-head column and use the line rows

\[
 H_{s,b}=X_b e_b(I-P_s),\qquad
 J_{t,c}=-\frac{A_t(c,a)X_c}{L_{tc}}\,vP^t,
 \quad P^t=\prod_{j\ne t}^{\nearrow}K_j.
 \tag{LC93}
\]

They are precisely the new-head and new-first source residues
divided by X_a. Let B_q be their 6q-square old-pole observation
matrix, with two zero-sum coordinates at each of the 3q nodes.
Its q=1 base is generically invertible directly: at the old pole
c the two exclusive columns have residues -X_c v_1c and
-A_1(c,a)X_c v. The two line normals are independent and all
coordinates are units, so these two rows are independent.

For q>=2 put P=K_1...K_(q-1), V=K_q^(-1), and
P_d={L_circle,a=L_qd=0}. At P_d replace the two residue
coordinates of a row Y by the pair consisting of the one
nonzero coordinate of Res(YV) and the canceled value

\[
 (YV)_d(P_d)
   =\left[\operatorname{Res}_{L_{qd}}Y\,
             \operatorname{diag}(X)^{-1}A_q^{-1}e_d\right]_{P_d}.
 \tag{LC94}
\]

This is an invertible change of observation coordinates.
Indeed the kernel of residue multiplication by V is
span(v_qd), and the canceled-value functional equals one on
v_qd. Inherited head columns become
H_(s,b)^(q-1)+X_b e_b(V-I), while inherited incoming columns
become exactly J_(t,c)^(q-1).

Choose j different from d and set
xi_d=(v_qd P V)_j(P_d), eta_d=(v P V)_j(P_d).
The nonzero xi_d are the proved new-head pivots. Both residue
rows have component d zero and row sum zero, so the actual
column combination
C_d=J_(q,d)-A_q(d,a)(eta_d/xi_d)H_(q,d)
has no q-block pole after multiplication by V. Let b_d be the
earlier-pole observations of C_d V. Assuming B_(q-1) invertible,
solve alpha_d=B_(q-1)^(-1)b_d and subtract the corresponding
actual transported inherited columns, including every
X_b e_b(V-I) head correction. Denote the remainder by T_d.

It is a homogeneous linear zero-sum polynomial row on the new
line. There are no remaining old-line poles. Coordinate
denominators cancel in X_b e_b V and in products P V, since
the last earlier kernel supplies diag(X); q>=2 is used here.
The remaining three observation coordinates give the exact
conditional equivalence

\[
 B_q\text{ invertible}
 \quad\Longleftrightarrow\quad
 \det S_q\ne0,\qquad
 S_q=\bigl((T_d)_c(P_c)\bigr)_{c,d=0,1,2},
 \tag{LC95}
\]

under the stated shorter-matrix and pivot hypotheses. This
follows by ordinary block elimination using (LC94): three new
head pivots, the 6(q-1) shorter observations, and these last
three canceled values.

For completeness, the evaluation map on degree-one zero-sum
polynomial rows has kernel exactly span(vV). If its c-th
component vanishes at P_c, that component is k_c L_qc on the
new line. Their sum vanishes iff k A_q is a multiple of the
new line normal, which gives precisely vV. This kernel does
not invalidate the square residue criterion: it is the
polynomial direction invisible to the original pole data.

The uniform nonvanishing of det S_q is unproved. Highest
confluent poles alone also yield only one pivot per node;
discarding the canceled values or the inherited polynomial
correction would lose the missing information. This recurrence
requires only the shorter paired boundary inverse, rather than
the full old source inverse. Even a proof of det S_q nonzero
would still leave the old-source Schur complement needed for
the original equation-(24) independence theorem.

## Recovering the accumulated head coefficients from endpoint data

The polynomial head corrections in (LC89) depend only on the
three accumulated head sums, not on every head coefficient
separately. These sums admit an exact endpoint formula. For q>=2,
write a paired-sector combination as
Y=sum_(s,b) x_sb H_sb+sum_(t,c) y_tc J_tc, and put
sigma_b=sum_s x_sb, h_s=sum_b x_sb X_b e_b,
mu_t=sum_c y_tc A_t(c,a)X_c/L_tc. All completed terms in Y
end in K_q except the six last-slot terms

\[
 E=(h_qK_q+\mu_q v)P^q,\qquad
 P^q=K_1\cdots K_{q-1}.
 \tag{LC96}
\]

They end in K_(q-1). At the coordinate-edge point
M_b={L_circle,a=X_b=0}, use the active two-state column vector
eta_(t,b)=A_t[hat b,hat b]^(-1)A_t[hat b,b]. A completed row
ending in K_t has a preceding row with component b divisible
by X_b. Its canceled output ratios therefore obey
(R_b/X_b)(M_b)=sum_(i different from b)
eta_(t,b,i)(R_i/X_i)(M_b).
All endpoint denominators and active principal minors are
assumed nonzero.

Define Phi_q(Y)_b=(Y_b/X_b)(M_b)
-sum_(i different from b)eta_(q,b,i)(Y_i/X_i)(M_b), and
Psi_q(E)_b=sum_(i different from b)
(eta_(q-1,b,i)-eta_(q,b,i))(E_i/X_i)(M_b).
The preceding identity gives

\[
 L_q\sigma=\Phi_q(Y)+\Psi_q(E),\qquad
 (L_q)_{bb}=1,\quad (L_q)_{bi}=-\eta_{q,b,i}\ (i\ne b),
 \quad
 L_q=\operatorname{diag}((A_q^{-1})_{bb})^{-1}(A_q^{-1})^{\mathsf T}.
 \tag{LC97}
\]

This is a new endpoint matrix L_q, not a row form L_qa.
It is invertible whenever A_q and its inverse diagonal entries
are nonzero. In the positive weighted family, write
w_i=1/r_i, S=1+sum_i w_i, and b_q=(1,u_q,v_q). Then
eta_(q,b,i)=(b_qb/b_qi)w_i/(S-w_b), and
det L_q=S^2/product_b(S-w_b)>0, independent of the time factors.
Thus this particular inverse introduces no new nonvanishing
problem in the weighted family.

The last-slot dependence can be reduced further. At P_c from
(LC94), choose an active component j and set
rho_c=-[Res_(L_qc)(YV)]_j/X_c,
xi_c=(v_qc P^q V)_j(P_c),
zeta_c=(v P^q V)_j(P_c), V=K_q^(-1).
All inherited columns are regular at this q-block pole after
transport, so
x_qc=(rho_c-A_q(c,a)zeta_c y_qc)/xi_c.
The nonzero xi_c are the same pivots as before.

For an explicit coefficient form, put
U_c=X_c e_c K_q P^q and
V_c=A_q(c,a)X_c vP^q/L_qc; the latter V_c is a row, distinct
from the inverse matrix V. Define parameter-only columns
C_q(:,c)=Psi_q(U_c)/xi_c and
D_q(:,c)=Psi_q(V_c-A_q(c,a)zeta_c U_c/xi_c). Then

\[
 \sigma=L_q^{-1}
       \bigl(\Phi_q(Y)+C_q\rho+D_q y_{\rm last}\bigr).
 \tag{LC98}
\]

The exceptional endpoint evaluations in (LC96) use only the
active two-state products at each M_b. Their finite list of
unknown coefficients is now the three last incoming y_qc:
no full list of shorter head coefficients is required to
compute their accumulated polynomial correction. This identity
holds for every actual paired-source combination, even without
assuming the paired source matrix invertible. It does not
recover y_last or prove det S_q nonzero. Those three remaining
coefficients, and their interaction with the canceled values
in (LC95), are the concrete next step.

## Explicit interpolation and the remaining three-coefficient feedback

The row interpolant needed in (LC95) can be constructed without
inverting the shorter paired source matrix. Choose an affine
coordinate z on the new line with all three coordinate-edge
points at distinct finite values tau_j, all old-pole nodes z_i
finite, and no node at an edge. For prescribed ordinary
z-residue rows r_i with sum_j r_ij=0, put

\[
 F^0_j(z)=\sum_i r_{ij}
       \frac{z-\tau_j}{(z_i-\tau_j)(z-z_i)},\qquad
 C=\sum_{i,j}\frac{r_{ij}}{z_i-\tau_j}.
 \tag{LC99}
\]

The partial-fraction identity
(z-tau_j)/((z_i-tau_j)(z-z_i))
=1/(z_i-tau_j)+1/(z-z_i)
shows that sum_j F^0_j=C. Therefore
F_j=F^0_j+c_j(z-tau_j), where
c_0=C/(tau_0-tau_1), c_1=-c_0, c_2=0,
has row sum zero, the prescribed residues, and component j
zero at its coordinate edge. Restoring the homogeneous chart
factor gives a degree-one row R_can. Any other row with these
properties, no additional poles, and affine growth at most
one differs from R_can by lambda v. Indeed the difference is
a degree-one polynomial, component j is a multiple of X_j,
and its zero sum makes the three coefficients proportional
to the new line normal. The growth condition is essential:
unrestricted polynomial terms would invalidate uniqueness.
All original homogeneous residue observations must first be
converted consistently to these ordinary affine residues.

This polynomial ambiguity cancels in the transported quotient.
For fixed terminal residue data rho and fixed last incoming
coefficients, replacing the auxiliary representative R by
R+lambda v in (LC98) changes sigma by lambda A_circle(a,:).
This follows from Phi_q(v)=L_q A_circle(a,:)^T. Consequently

\[
 R+h_\sigma(V-I)\ \longmapsto\
 R+h_\sigma(V-I)+\lambda vV,\qquad
 h_\sigma=\sum_b\sigma_bX_b e_b.
 \tag{LC100}
\]

The added row is in the canceled-value kernel from (LC95).
This is a rule for auxiliary representatives; it does not
assert that adding lambda v preserves the actual paired
source span.

For an explicit feedback formula take q>=3 and k=q-1, so the
endpoint formula (LC98) applies to the shorter family. Suppose
B_k is invertible. For shorter residue data z, let T_k z be
the three last incoming coefficients of its unique actual
paired-source preimage. Define the known linear maps

\[
 \mathcal A_k z=L_k^{-1}
   \bigl(\Phi_k(R_{\rm can}(z))+C_k\rho(z)\bigr),
 \qquad
 \overline D_k=L_k^{-1}D_k.
 \tag{LC101}
\]

Here rho(z) is the shorter terminal transformed-residue
observation, obtained linearly from z. In the representative
gauge R_can, (LC98) gives
sigma=mathcal A_k z+overline D_k T_k z. The actual preimage
may differ from R_can by lambda v, but (LC100) cancels this
difference in every following canceled-value test.

Let b_q be the three earlier-residue columns of C_d V_q in
(LC95), and let Eval_q take component c at P_c. With
X_q=diag(X_c(P_c)), the exact remaining matrix is

\[
 \begin{aligned}
 S_q&=S_q^{\rm local}
       +X_q\overline D_k(T_k b_q),\\
 S_q^{\rm local}
   &=\operatorname{Eval}_q
        \bigl((C_dV_q)_{d=0}^2-R_{\rm can}(b_q)\bigr)
       +X_q\mathcal A_k b_q .
 \end{aligned}
 \tag{LC102}
\]

Here interpolation and evaluation act columnwise on the
three indicated rows. The plus signs follow because column c of V_q vanishes at
P_c: the c-th component of h_sigma(V_q-I) there equals
-X_c sigma_c, and this inherited correction is subtracted.
For q=2 one must use the direct shorter base separately;
(LC101) does not invoke the q>=2 endpoint formula at k=1.

Equations (LC99)--(LC102) were independently audited. They
remove the full shorter inverse from constructing the row
interpolant and isolate its remaining effect in the three
last incoming coefficients. They do not yet give a closed
recurrence with a fixed number of state variables: T_k still
has a growing residue-data domain. Proving a closed formula
for its action on b_q, or proving the resulting determinant
nonzero directly, remains open.

## The endpoint derivative at a last-time collision

There is a regular way to study the same correction when the
last two time blocks coincide. Write k=q-1, K_k=K,
K_q=K+epsilon dotK+O(epsilon^2), and
P=K_1...K_(k-1). Vary the last time factors by
b_qi=b_ki(1+epsilon delta_i)+O(epsilon^2). Use the actual
duplicate differences Y_epsilon=H_qb-H_kb or J_qc-J_kc
in the q-block family, without dividing by the possibly
singular Newton pivots xi. They vanish at epsilon=0 and
have total head-prefix sum zero identically. Their positive
exceptional completed rows in (LC96) specialize respectively to
E_0=X_b e_b KPK and
E_0=A_k(c,a)X_c vPK/L_kc. Differentiating (LC97) gives

\[
 \Phi_K(Y')_b
   =\sum_{i\ne b}\dot\eta_{bi}(E_{0,i}/X_i)(M_b),
 \qquad
 \dot\eta_{bi}=(\delta_b-\delta_i)\eta_{k,b,i}.
 \tag{LC103}
\]

The sign is positive: the exact identity for these differences
is 0=Phi_q(Y_epsilon)+(eta_k-eta_q)(E_epsilon/X),
and Y_0=0. In particular eta_q-eta_k being of first order
does not make the correction negligible; its first coefficient
is generally nonzero.

The corresponding derivative is supported on just the six
terminal columns of the shorter paired family. For each such
family column define the auxiliary polynomial prefix by
I_aux(H_sb)=X_b e_b and I_aux(J_tc)=0. This auxiliary prefix
is distinct from the global source-prefix map. With only
the shorter last time varied, define on each column

\[
 \nabla R=\dot R-(R-I_{\rm aux}(R))\dot K K^{-1}.
 \tag{LC104}
\]

Every nonterminal completed word ends in K, so its derivative
is (R-I_aux(R))dotK K^(-1), and its connection value is zero.
For the last six columns, putting g_c=A_k(c,a)X_c/L_kc gives

\[
 \begin{aligned}
 \nabla H_{k,b}
   &=-X_b e_b\dot K P+X_b e_bKP\dot K K^{-1}
     =(H_{q,b}-H_{k,b})'K^{-1},\\
 \nabla J_{k,c}
   &=-\dot g_c\,vP+g_c vP\dot K K^{-1}
     =(J_{q,c}-J_{k,c})'K^{-1}.
 \end{aligned}
 \tag{LC105}
\]

These are identities for the actual ordered columns and their
coefficientwise linear extension. Differentiating a combination
whose coefficients themselves vary would additionally
differentiate those coefficients.

There is still a source-compatibility condition. Set
sigma*=L_K^(-1)Phi_K(Y') and
f*=Y'K^(-1)-h_sigma*(K^(-1)-I).
The inverse-column identity behind (LC97) makes f* satisfy
the shorter coordinate-edge conditions. Once all residual
double poles are removed, this constructs a shorter ambient
interpolant. It does not prove that sigma* equals the
accumulated head coefficients of the actual shorter source
preimage. That discrepancy is precisely the remaining
confluent graph condition, modulo the gauge in (LC100).
The identities (LC103)--(LC105) passed independent audit;
nonvanishing of the final three pivots remains unproved.

## Strengthening the new-head theorem to every fixed positive weight triple

The nonzero Newton-pivot proof in (LC88)--(LC89) can be
strengthened: r need not vary. This argument was proposed in
[Pro41](https://chatgpt.com/c/6ad1b27c-7cb0-83ed-b39d-e1350c9e67c7)
and independently audited locally.

Fix positive r and a generic last time. At the point
P*={L_circle,a=L_md=0}, all X coordinates are units, and
V=K_m^(-1)(P*) has rank two with left kernel span(v_md).
Choose a zero-sum row w satisfying
w_0=(r_0+1)X_0 and w not parallel to v_md. Set the two
auxiliary time factors to w_1/X_1 and w_2/X_2. Its row-zero
numerator is w and its row-zero denominator vanishes.
Writing c_0=r_0+1 and w_2=-c_0X_0-w_1, the other two
denominators are

\[
 L_{h1}=-r_0X_0+r_1w_1,\qquad
 L_{h2}=[1-c_0(r_2+1)]X_0-r_2w_1.
 \tag{LC106}
\]

They exclude only finitely many choices of w_1, as do
w_1w_2=0 and w parallel to v_md. Move every earlier time
toward this same auxiliary time with L_h0(P*)=epsilon.
Then K_h(P*)=epsilon^(-1)e_0w+O(1), and for m>=2

\[
 v_{md}K_h^{m-1}V
  =\epsilon^{-(m-1)}(v_{md})_0w_0^{m-2}wV
       +O(\epsilon^{-(m-2)})\ne0.
 \tag{LC107}
\]

Every factor in the leading coefficient is nonzero by the
choices above. The auxiliary limiting times need not be
positive: this specialization proves that the relevant real
rational function is not identically zero. Its nonvanishing
open set then intersects the positive time orthant. For each
finite m, the finitely many pivot conditions and generic
geometry conditions can be imposed simultaneously there.
The m=1 direct base and the induction in (LC89) therefore
prove full new-head residue rank 9q for every fixed positive
r, including r=(2,3,5).

The same pivot construction works for a fixed positive common
G with det G nonzero and all two-by-two minors nonzero.
Use w_0=G_00X_0 and auxiliary factors
w_1/(G_01X_1), w_2/(G_02X_2). The other-row denominators
are affine functions of w_1 with slopes
G_i1/G_01-G_i2/G_02, nonzero by the stated minors. The
geometric open conditions and the direct base then give the
same new-head theorem. Invertibility of G is a separate
assumption; the two-by-two minor conditions alone do not
imply it. Neither version proves a rank contribution modulo
retained old columns.

## Constructive quotient by the entire new-head family

Pro41 also supplied the following independently audited
construction. Fix a new-line sector, write g=A_circle(a,:)^T,
and let mathcal V_m be the degree-one, zero-sum rational rows
with simple poles at the 3m old nodes and component j zero
at Q_j={L_circle,a=X_j=0}. Its dimension is 6m+1 and its
polynomial subspace is span(v).

For rows regular at the coordinate edges define
e(F)_j=F_j(Q_j). Choose k(j) different from j and the
zero-sum polynomial rows W_j=X_k(j)(e_j-e_k(j))/X_k(j)(Q_j).
They satisfy e(W_j)=e_j. Thus every degree-one zero-sum
polynomial row has the unique decomposition
F=sum_j e(F)_j W_j+phi(F)v. The functional phi is used
only on polynomial rows.

Put V_m=K_m^(-1), U_sb^(m)=H_sb^(m)-H_1b^(m), s>=2,
and J_mb^poly=X_b e_b(V_m-I). The latter notation denotes
a polynomial head correction, not an incoming source.
For any f_m in mathcal V_m determine x_md from
Res_(L_md)(f_m V_m)=x_md Res_(L_md)(U_md^(m)V_m).
The residue image is one-dimensional and the pivot is the
proved nonzero head pivot. Define

\[
 G_m=\left(f_m-\sum_b x_{mb}U_{mb}^{(m)}\right)V_m,
 \qquad y_m=e(G_m),\qquad
 f_{m-1}=G_m-\sum_j(y_m)_jW_j .
 \tag{LC108}
\]

There are no newest-block poles in G_m and no coordinate
poles: the component factors X_j cancel diag(X)^(-1)
in V_m. Subtracting the polynomial edge correction gives
f_(m-1) in mathcal V_(m-1). Conversely,
f_m=sum_b x_mb U_mb^(m)+(f_(m-1)+sum_j y_mj W_j)K_m.
The differences transport exactly:
U_sb^(m)K_(m+1)...K_q=U_sb^(q).

At m=1 choose three complementary one-node residue lifts
g_d alongside the three H_1b^(1) and v. Each g_d has
residue at only node d, independent there of the H_1d
residue. Existence follows by prescribing residues and
subtracting polynomial edge values. These seven rows
form a basis, so the final row has a unique expansion

\[
 f_1=\sum_b\beta_b H_{1b}^{(1)}
          +\sum_d\gamma_d g_d+\lambda_1v .
 \tag{LC109}
\]

Define the edge matrix and polynomial coefficient row

\[
 \mathcal E_m=
  \bigl(e(J_{m0}^{\rm poly}),e(J_{m1}^{\rm poly}),
        e(J_{m2}^{\rm poly})\bigr)
  =\operatorname{diag}(L_{mj}(Q_j))(A_m^{-1})^{\mathsf T},
 \qquad
 \eta_m=(\phi(J_{m0}^{\rm poly}),\phi(J_{m1}^{\rm poly}),
                  \phi(J_{m2}^{\rm poly})).
 \tag{LC110}
\]

This matrix is invertible on the stated coordinate-edge
geometry. It is distinct from the endpoint matrix L_m
and its coefficients eta in (LC97). Set z_m=mathcal E_m^(-1)y_m.
On a baseline head combination plus lambda_m v, the exact
relations are z_m=beta+lambda_m g and
z_(m-1)=(I+g eta_m)z_m. No inverse of this rank-one
update is needed. For q>=2 define the 3q quotient observations

\[
 \mathcal C_a(f)=
 \left(
  \gamma,\
  \bigl(z_{m-1}-(I+g\eta_m)z_m\bigr)_{m=3}^q,\
  \beta+\lambda_1g-(I+g\eta_2)z_2
 \right).
 \tag{LC111}
\]

Their kernel is exactly span(H_sb^(q)) direct-sum span(v).
Necessity follows by transporting each difference and using
the baseline relations. For sufficiency the last relation
sets z_1=beta+lambda_1g, and each transition changes z_m
only by a multiple of g. Hence every z_m-beta is a multiple
of g; reconstruction in (LC108) gives precisely a head
combination plus a multiple of v. At q=1 use gamma as
the three quotient observations.

The extracted head coefficients are c_sb=x_sb for s>=2,
c_1b=beta_b-sum_(s>=2)x_sb. This defines a projection Pi_a
which recovers the coefficients on the head span. Both Pi_a
and mathcal C_a kill v, and together they give an invertible
change of the 6q residue coordinates. For the original
physical new-head columns divide c_sb by A_circle(a,b);
their accumulated literal head margin is beta.
This is an explicit descent with a fixed seven-dimensional
base and three pole/three edge operations at each length.
The rational input and residue data still grow with q:
it is not a closed recurrence for the paired determinant.

## Exact old/new source elimination using the explicit head quotient

Let N be all 9q actual new-head F columns, T all retained
old-head/old-first columns, and B all 9q old-head/new-first
columns. Across the three sectors the preceding maps give
(Pi_N,C) as an invertible change of the 18q new-pole rows,
with Pi_N D_new(N)=I and C D_new(N)=0.
The profiles supplied to that descent are actual ordered
source residues:

\[
 \left.\frac{L_{\circ a}}{X_a}F^+_{t,s,h,b}\right|_{L_{\circ a}=0}
   =-\frac{p_{thb}A_s(b,a)}{L_{sb}}\,v_aR_{ts},
 \qquad
 \left.\frac{L_{\circ a}}{X_a}F_{t,\circ,h,b}\right|_{L_{\circ a}=0}
   =-\delta_{ba}\frac{X_hA_t(h,a)}{L_{th}}\,v_aR_t .
 \tag{LC112}
\]

Here R_ts omits t,s and R_t omits t, both increasing.
In particular the inserted K_s contributes the factor
A_s(b,a)/L_sb and has not been dropped. The incoming
quotient C_B separates into three 3q-square state sectors.

Write T=F_old+A_err, with the exact prepend error
A_err,ts,hb=p_thb e_b K_s(I-K_circle)R_ts. Subtract the
actual head projections from T and B, and set
Z_T=D_old(A_err-N Pi_T), Z_B=D_old(B-N Pi_B).
Ordinary invertible row and column operations give

\[
 D_{q+1}\sim
 \begin{pmatrix}
 I_{9q}&0&0\\
 0&D_q+Z_T&Z_B\\
 0&C_T&C_B
 \end{pmatrix}.
 \tag{LC113}
\]

This elimination does not assume D_q invertible. If it is
invertible, one may factor det D_q from the lower block,
retaining I+D_q^(-1)Z_T rather than replacing it by I.
No nonvanishing of that remaining block is proved.
The literal new-head margins after subtraction are -beta_a(T)
and -beta_a(B). Their actual matching observations remain
-beta_a(X)+A_circle(a,:)e_circle,a(X-N Pi_X); they must
not be counted again as residue pivots.

For the paired boundary problem there is an additional exact
delay property: when t<m,
J_tc^(m)V_m=J_tc^(m-1), so its descent has x_m=y_m=0
until m reaches t. Applying (LC111) to these delayed
incoming columns may expose a useful matrix structure.
The newest incoming group still produces earlier residues,
so this property alone does not make C_B triangular or
prove its determinant nonzero.

## The direct canceled-value term is a nonzero diagonal matrix

Before the inherited correction in (LC95), the three canceled
columns already have an explicit nonzero diagonal evaluation.
At P_d, write P=K_1...K_(q-1) and use any fixed exterior
coordinate on the two-dimensional zero-sum row plane. Then

\[
 \operatorname{Eval}_q\bigl((C_dV_q)_{d=0}^2\bigr)
      =\operatorname{diag}(\kappa_0,\kappa_1,\kappa_2),
 \qquad
 \kappa_d=
 X_d A_q(d,a)\det(P|_{\mathbf1^\perp})
 \frac{v\wedge v_{qd}}{(v_{qd}P)\wedge v_{qd}} .
 \tag{LC114}
\]

All quantities in column d are evaluated at P_d. The
denominator is nonzero precisely when the already-used
transformed head pivot is nonzero. The numerator is
nonzero on the geometric open set: the two line normals
are independent, all coordinates are units, and all earlier
kernels are invertible at P_d.

To check the formula, put r_d=A_q(d,a)zeta_d/xi_d.
The original residue of C_d is
X_d(r_d v_qd-A_q(d,a)v)P. Its product with V_q vanishes,
so it equals kappa_d v_qd. Wedge this identity with
v_qd P and use the determinant of P on the zero-sum plane
to obtain (LC114), including its sign. The canceled-value
functional in (LC94) equals one on v_qd. At any other
newest node P_c, C_d is regular and column c of V_q
vanishes, giving the off-diagonal zeros.

Thus singularity of S_q cannot come from a missing direct
diagonal pivot. It can still come from cancellation with the
actual shorter interpolation correction:
S_q=diag(kappa_d)-Eval_q(transported shorter preimages).
No bound, sign, or vanishing of that correction follows
from the diagonal formula.

The saved finite checker
[source24_boundary_recurrence.py](../exploration/source24_boundary_recurrence.py)
independently reconstructs (LC94)--(LC95) in sector a=0
from the previously saved weighted three- and four-block
source matrices. In its normalized affine chart the actual
old-q=2,3 remaining determinants are 671017 and 930959
modulo 1000003. It verifies the shorter head corrections
against actual words, both residue coordinates, the block
determinant factorizations, (LC98), and the plus sign and
polynomial gauge in (LC102). The feedback term is nonzero
in this fixture. Its ordinary-word affine-remainder controls
use more points than the cleared polynomial degree, so they
certify the corresponding finite-field identities. The
source matrices were not regenerated and no parameters were
searched. One guarded run passed in 0.17 seconds with peak
RSS 19,447,808 bytes. This remains a finite certificate,
not a uniform determinant theorem or a Lean proof.

## The incoming edge pivots equal the endpoint coupling

There is an exact link between the descent in (LC108) and
the endpoint formula (LC98). For t>=2 and each incoming
column define

\[
 R_{tc}=J_{tc}^{(t)}-r_{tc}U_{tc}^{(t)},\qquad
 r_{tc}=A_t(c,a)\zeta_{tc}/\xi_{tc},\qquad
 Y_t(:,c)=e(R_{tc}V_t),\qquad Z_t=\mathcal E_t^{-1}Y_t .
 \tag{LC115}
\]

Here Y_t is a three-by-three matrix, not an original source
row. The head difference U_tc has accumulated head sum zero.
Consequently R_tc has zero head sum, zero newest transformed
residue rho, and last incoming coefficient vector e_c.
Equation (LC98) gives Phi_t(R_tc)=-D_t(:,c). For every
coordinate-divisible row regular at the edges,

\[
 e(RV_t)=
 \operatorname{diag}\bigl(L_{tj}(Q_j)(A_t^{-1})_{jj}\bigr)
 \Phi_t(R),\qquad
 \mathcal E_t=
 \operatorname{diag}\bigl(L_{tj}(Q_j)(A_t^{-1})_{jj}\bigr)L_t .
 \quad\text{Thus}\quad
 Z_t=-L_t^{-1}D_t=-\overline D_t .
 \tag{LC116}
\]

This uses undivided edge values after inverse transport,
and canceled coordinate ratios before transport. Confusing
the two evaluations would change the matrix. The diagonal
entries of Y_t and D_t are zero: at Q_c the active
coordinate ratios of the completed terms in R_tc vanish,
because their input has a factor X_c and the earlier
product is nonempty. The endpoint identity then gives the
remaining canceled component. The normalized matrix Z_t
need not have zero diagonal.

Choose the one-node complementary lifts in (LC109) to be
the actual incoming columns J_1d, using the direct paired
one-node base. Take incoming groups t=1,...,q-1 and only
the quotient rows gamma and the defects indexed m=3,...,q
in (LC111). The delay property makes this square submatrix
block upper triangular, in those orders, with diagonal

\[
 I_3,\ Z_2,\ldots,Z_{q-1}.
 \tag{LC117}
\]

Indeed an incoming group t has z_m=0 above level t, and
its first edge value is z_t=Z_t. Its defect in row m=t+1
is therefore Z_t; all later defect rows vanish. Earlier
defects may be nonzero, which is why this is a submatrix
statement rather than triangularity of the entire quotient.
If D_2,...,D_(q-1) are invertible, these 3(q-1) incoming
columns are independent modulo all 3q heads and the
polynomial row v. Hence the paired residue rank is at
least 6q-3 in that sector. For q=2 the list of D conditions
is empty. This conclusion does not assume shorter paired
matrices invertible. The three remaining quotient rows and
the last incoming group still require a determinant argument.

The local independent audit checked the sign, normalization,
and block ordering in (LC115)--(LC117). The separate saved
finite probe
[source24_boundary_edge_pivots.py](../exploration/source24_boundary_edge_pivots.py)
uses the already saved recurrence data and finds det Z_2
=345725 and det Z_3=378997 modulo 1000003 in sector zero.
Both have rank three, and their unnormalized Y matrices
have zero diagonal. Its single guarded run took 0.17 seconds
with peak RSS 18,612,224 bytes. These checks alone do not
prove the conditions of (LC117) at arbitrary length.

## Uniform nonvanishing of the endpoint coupling

The endpoint condition in (LC117) can now be proved for
every length. This argument was proposed in
[Pro43](https://chatgpt.com/c/6ad1b6c5-4e90-83ed-9a86-e33effd8d4c1);
two local audits independently derived its canceled-edge
formula, leading determinant, and genuine perturbation.
It is a paper theorem, not a Lean theorem.

Fix r=(1,1,1), so G=I+11^T, and start with sector a=0,
new time (1,1,1), and g=(2,1,1). Let m=q-1>=1.
Time vectors may be multiplied by a common nonzero scalar:
K, H, J, the cancellation ratios, and the endpoint
coupling D_q are unchanged. Put Y_i=g_i X_i, so that
the new line is sum_i Y_i=0 and v=Y. First let all m
earlier time vectors approach g, while the last one is
b_q=g componentwise multiplied by z. Write

\[
 t_m=(4^m-1)/3,\qquad s_m=(3^m-1)/2,\qquad
 U=\sum_i z_i,\quad T=\sum_i z_i^{-1}.
 \tag{LC118}
\]

At an interior point of the new line the limiting kernel
is K_*=I+d v, where d_i=1/Y_i and vd=3. Thus the
actual ordered product tends to P_*=I+t_m d v.
At the last node L_qc=0, v_qc V_q=0 and
v_qc d=U+z_c. Consequently the cancellation ratio tends to

\[
 r_c=\frac{A_q(c,a)4^m}{t_m(U+z_c)}.
 \tag{LC119}
\]

At a coordinate edge Q_b one must first evaluate the
actual canceled products on the active two-state block.
That block has v_active d_active=2, so its m-fold product
is I+s_m d_active v_active. Substituting the full
three-state limiting kernel at the edge would incorrectly
replace this 3^m dependence by 4^m.

For b different from c let e be the third state. The
limiting endpoint coupling has zero diagonal and

\[
 \widehat D_q(b,c)=
 \frac{b_{qa}g_b}{3(2z_c-z_e)}
 \left[
 3^m(3-z_bT)
 -\frac{4^m}{t_m(U+z_c)}
 \left\{U+z_c-4z_b+
 s_m(U+z_c-z_b)(3-z_bT)\right\}
 \right].
 \tag{LC120}
\]

Here a=0 and b_qa=2z_0 before normalizing the time vector.
For a direct check, eta_(q-1,b,i)-eta_(q,b,i) tends to
g_b(1-z_b/z_i)/(3g_i). At Q_b take the exceptional
completed row E_c=(A_q(c,a)X_c v/L_qc-r_c X_c e_c K_q)P.
Its active ratios, expressed after division by Y_i, are

\[
 \frac{b_{qa}Y_c}{L_{qc}}
 \left[
 3^m-\frac{4^m}{t_m(U+z_c)}
 \{z_i(1+\delta_{ic})+s_m(U+z_c-z_b)\}
 \right].
\]

Also Y_c/L_qc=1/(2z_c-z_e). The two required sums over
i different from b are 3-z_bT and U+z_c-4z_b.
Their substitution gives (LC120), including its sign.
All denominators in (LC120) are units near z=(1,1,1).

Define

\[
 k_m=\frac{3\,4^{m-1}}{4^m-1},\qquad
 \chi_m=3^m-\frac{3k_m}{2}(3^m-1),\qquad
 p_m=3^m(3k_m-2),\quad
 \ell_m=\chi_m-k_m,\quad d_m=\chi_m-2k_m .
 \tag{LC121}
\]

Expanding (LC120) along z=(1+epsilon,1,1) gives

\[
 \widehat D_q=
 \epsilon
 \begin{pmatrix}
 0&4p_m/3&4p_m/3\\
 2d_m/3&0&2\ell_m/3\\
 2d_m/3&2\ell_m/3&0
 \end{pmatrix}
 +O(\epsilon^2),\qquad
 \det\widehat D_q=
 \frac{32}{27}p_m\ell_md_m\,\epsilon^3+O(\epsilon^4).
 \tag{LC122}
\]

The coefficient is strictly positive for every m>=1.
Indeed ell_m=(k_m-p_m)/2, d_m=-(k_m+p_m)/2, and
p_m/k_m=3^(m-1)(1+8/4^m)>1. Thus p_m>k_m>0,
ell_m<0, and d_m<0. Equivalently the coefficient is
8 p_m(p_m^2-k_m^2)/27.

The calculation direction itself is geometrically degenerate;
the following separated perturbation is a genuine witness:

\[
 b_q=g\odot(1+\epsilon,1+\epsilon^2,1+2\epsilon^2),
 \qquad
 b_s=g\odot(1+\delta\alpha_{s0},
           1+\delta\alpha_{s1},1+\delta\alpha_{s2}),
 \quad 1\le s\le m,\qquad
 \delta=\epsilon^{2m+6}.
 \tag{LC123}
\]

Choose fixed generic positive alpha_si, take epsilon small
and positive, and normalize each time vector by its first
entry. At the three last nodes the matching coordinate has
orders epsilon^2, epsilon, epsilon respectively; the other
two coordinates are units after a bounded choice of
representative. The earlier kernels and their ideal limits
are O(epsilon^(-2)); their differences are
O(delta epsilon^(-4)). Telescoping the ordered m-factor
product gives error O(delta epsilon^(-2m-2)), and V_q
is O(epsilon^(-2)). Thus the errors in the quantities
defining xi_c and zeta_c are O(epsilon^2).

Their ideal denominators remain units. More explicitly,
(vV_q)_j=L_qj(1/z_j-T/4) tends to Y_j/4. Choose an
active j different from c with Y_j nonzero in the limit.
Equation (LC119) follows from xi_c=t_m(U+z_c)zeta_c,
so the cancellation ratios also have O(epsilon^2) errors.
At the coordinate edges the active binary products and eta
are regular in the earlier perturbations. Hence the actual
coupling is D_q=widehat D_q(z)+O(epsilon^2), preserving
the leading matrix and nonzero cubic determinant in (LC122).
Generic alpha avoids the finitely many incidence equations.
This proves generic det D_q nonzero for each q>=2 at
the fixed weight triple (1,1,1), with positive time witnesses.

Permuting states proves the same theorem in the other two
new-line sectors. For any fixed q, the finitely many
nonvanishing conditions for all lengths up to q-1 and
all sectors have a common nonempty open subset of the
positive time parameter space. Their simultaneous validity
does not require the separate witnesses to be identical.

Combining (LC116)--(LC117) with this theorem yields, for
every q>=2, generic paired boundary rank at least 6q-3
in each sector and at least 18q-9 over all three sectors.
Equivalently, the incoming quotient C_B in (LC113) has
rank at least 9q-9. These bounds hold already at fixed
r=(1,1,1), hence also generically when the common weights
vary. This proof does not assert the same statement for
every other fixed positive weight triple.

Only three incoming directions per sector remain after
the triangular elimination. Proving their final three-by-three
determinant nonzero is still open. Even full paired boundary
rank would leave the retained-old-source block in (LC113);
the equation-(24) independence theorem for all T is therefore
still open.

The exact symbolic companion
[source24_endpoint_coalescence.py](../exploration/source24_endpoint_coalescence.py)
expands (LC120) on both curves through cubic order in
Q[k_m,3^m][epsilon]/(epsilon^4). It checks the first matrix
and cubic determinant in (LC122), and separately clears
k_m=3A/[4(A-1)] with A=4^m, B=3^m. The determinant
coefficient simplifies to
B(A+8)((A+8)^2 B^2-9A^2)/(216(A-1)^3).
Its single exact run passed in 0.13 seconds with peak
RSS 14,073,856 bytes. It checks algebra of the supplied
formula; the actual-source identification and perturbation
proof above are separate mathematical arguments.

The coefficient algebra is now also checked in
SourceEndpointCoalescenceCoefficient.lean. Its ten declarations
prove the displayed determinant positive for A>1 and B>=3,
including A=4^m and B=3^m for every m>=1. The focused
build and axiom check passed. The source-family aggregate
checks 489 declarations in a 44-module compiled closure,
using only the permitted foundational axioms. Identification
with the actual asymptotic matrix and the uniform paired-rank
deduction remain paper arguments.

The fixed equal-weight finite probe
[source24_equal_weight_boundary.py](../exploration/source24_equal_weight_boundary.py)
directly constructs only the paired matrices at q=2,3,4,
with new time (1,1,1) and old b_t=(1,8^t,8^(2t)).
All three sectors have full ranks 12,18,24, respectively.
Their determinants modulo 1000003 are
(840657,491388,336677), (835722,440639,265972), and
(474096,257877,896587). The complete arrangement geometry
passes, and a separate polynomial-clearing calculation
checks all three components of every residue vector.
One guarded run took 0.17 seconds with peak RSS
16,564,224 bytes. These are finite generic bases within
fixed r=(1,1,1), not an all-length theorem. In particular,
there is no identically singular equal-weight family at
any of these three lengths.

## Why the final three directions need an additional splitting calculation

The endpoint witness does not immediately prove full paired
rank. At its exact preserving limit let B=I+d v, with
d_i=1/Y_i, and let all m earlier kernels equal B.
Write P=B^m, keep the last kernel K_q arbitrary, and use
the unnormalized earlier time vector g. Every earlier
incoming row collapses to the same function
J^circ=-g_a 4^(m-1)vK_q. With the cancellation ratio
in (LC119), direct multiplication gives

\[
 J_{qc}-r_c U_{qc}
   =-\frac{b_{qa}4^m}{U+z_c}\,vK_q
   =\frac{4b_{qa}}{g_a(U+z_c)}\,J^\circ .
 \tag{LC124}
\]

Indeed U_qc=X_c e_c(PK_q-K_qP), and
e_c K_q d=(U+z_c)/L_qc. Substituting P=I+t_m d v
cancels the v term exactly. Thus the remaining quotient
columns already lie in the collapsed earlier incoming
span at zeroth order. The genuine earlier-time splitting
cannot be discarded in an attempted proof of the last
three directions.

For an explicit next calculation vary only earlier block
ell by b_ell,i=g_i(1+epsilon delta_i), holding K_q fixed.
Put W=sum_i delta_i Y_i and N=dv. Then

\[
 (\dot B)_{i,:}
  =\frac{v(\operatorname{diag}(\delta)-\delta_i I)}{Y_i}
    -\frac{Wv}{Y_i^2}-\frac{W e_i}{Y_i},
 \qquad
 \dot P=B^{\ell-1}\dot B B^{m-\ell}.
 \tag{LC125}
\]

Let mu_qc=A_q(c,a)X_c/L_qc and
k_c=4b_qa/(g_a(U+z_c)). For the relation in (LC124),
represented using any J_ell,h, keep r_c and k_c fixed
at their limiting values. Its first derivative is

\[
 -\mu_{qc}v\dot P
 -r_c X_c e_c(\dot P K_q-K_q\dot P)
 +k_c g_a\left(\delta_a-\delta_h-\frac W{Y_h}\right)
       4^{m-1}vK_q .
 \tag{LC126}
\]

This follows because J_ell,h omits the varying block:
only its exterior scalar differentiates. Since N^2=3N,
dot P lies in the span of dot B, N dot B, dot B N,
N dot B N, with explicit coefficients from
B^j=I+(4^j-1)N/3. These identities have been checked
algebraically. Their independence after correcting the
simultaneously splitting earlier columns is unproved;
the four-term expression alone does not give the final
three pivots.

## An explicit three-scalar interface independent of the appended time

[Pro42](https://chatgpt.com/c/6ad1b460-b4cc-83ed-8db3-abba27d943ac)
supplied a different description of the inherited correction,
checked independently locally. Take sector a=0, put
k_i=1+r_i, g=(k_0,1,1), and use coordinate-edge
representatives Q_0=(0,1,-1), Q_1=(1,0,-k_0),
Q_2=(1,-k_0,0). Write m=q-1 and A=A_q. The actual
polynomial head correction for a constant row h is

\[
 \Phi_A(h)=h\operatorname{diag}(X)(V_q-I)
          =hA^{-1}\operatorname{diag}(L_q)
             -h\operatorname{diag}(X).
 \tag{LC127}
\]

Every homogeneous linear zero-sum polynomial row T has
a unique decomposition T=cv+Phi_A(h). The three
undivided edge values recover h, and one further scalar
value recovers c. More generally, for any zero-sum
rational row W regular at the coordinate edges define

\[
 h_A(W)=
   \left(\frac{W_i(Q_i)}{L_{qi}(Q_i)}\right)_{i=0}^2 A,
 \qquad
 c_A(W)=\bigl(W-\Phi_A(h_A(W))\bigr)_1(Q_0),
 \qquad d_A(W)=h_A(W)-c_A(W)g .
 \tag{LC128}
\]

The chosen representative has v_1(Q_0)=1. This
four-value functional is defined on rational rows;
only the decomposition assertion requires W polynomial.
It obeys d_A(Phi_A(h))=h, d_A(v)=-g,
d_A(vV_q)=0. For a polynomial row T,
Eval_q(T)=-diag(X_c(P_c))d_A(T)^T.

Let R(c) be an actual shorter paired combination, h(c)
its three accumulated head coefficients, and
ell_0(R)=R_1(Q_0). Its coordinate factors imply
h_A(R)=0 and d_A(R)=-ell_0(R)g. Thus the inherited
interface is the constant row
mu(c)=h(c)-ell_0(R(c))g. Unlike d_A itself, this
interface depends only on the shorter family and the
fixed new line, not on the appended time.

There is an explicit source table for it. At Q_0 let
R_t be the active two-state restriction of K_t, put
d_12=k_1k_2-1, and set

\[
 \delta_t=\det R_t
   =-\frac{d_{12}u_tv_t}
      {(k_1u_t-v_t)(u_t-k_2v_t)},\quad
 \Delta=\prod_{t=1}^m\delta_t,\quad
 p_s=\left(R_s\prod_{j\ne s}^{\rm increasing}R_j\right)_{12}.
 \tag{LC129}
\]

These are the actual selected-first words. Their other
off-diagonal entry is 1-Delta-p_s. Consequently
ell_0(H_s0)=0, ell_0(H_s1)=p_s,
ell_0(H_s2)=1-Delta-p_s, and

\[
 \ell_0(J_{t0})=0,\qquad
 \ell_0(J_{t1})=\frac{\Delta}{d_{12}}
          \left(\frac1{v_t}-\frac{k_2}{u_t}\right),\qquad
 \ell_0(J_{t2})=\frac{\Delta}{d_{12}}
          \left(\frac1{u_t}-\frac{k_1}{v_t}\right).
 \tag{LC130}
\]

For example the incoming deletion tail multiplies the
zero-sum active row by Delta/delta_t; its exterior
A_t(c,0)X_c/L_tc factor gives (LC130). Define
U=[[1,0,-k_0],[0,1,-1],[0,0,1]] and let the
three-row coefficient map mathcal I_m satisfy
mathcal I_m c=U mu(c)^T. Its columns are

\[
\begin{array}{c|c}
 H_{s0}&(1,0,0)^{\mathsf T}\\
 H_{s1}&(0,1,-p_s)^{\mathsf T}\\
 H_{s2}&(-k_0,-1,\Delta+p_s)^{\mathsf T}\\
 J_{t0}&0\\
 J_{t1}&(0,0,\frac{\Delta}{d_{12}}(k_2/u_t-1/v_t))^{\mathsf T}\\
 J_{t2}&(0,0,\frac{\Delta}{d_{12}}(k_1/v_t-1/u_t))^{\mathsf T}.
\end{array}
 \tag{LC131}
\]

Every head triplet has determinant Delta, which is
nonzero on the coordinate-edge geometry. The first two
rows are unweighted head margins; all incoming source
dependence enters one explicit scalar endpoint balance.

Now assume B_m invertible, take W_d=C_dV_q from
(LC95), let b_d be its earlier residue data, and
alpha_d=B_m^(-1)b_d. The actual polynomial remainder is
T_d=W_d-R(alpha_d)-Phi_A(h(alpha_d)). Therefore

\[
 U\operatorname{diag}(X_c(P_c))^{-1}S_q
  =\mathcal I_m B_m^{-1}[\,b_0\ b_1\ b_2\,]
       -[\,U d_A(W_d)^{\mathsf T}\,]_{d=0}^2 .
 \tag{LC132}
\]

This preserves the inherited head correction exactly.
It replaces its description by three explicit dual rows
mathcal I_m B_m^(-1), independent of the appended time.
Those rows still act on a growing residue-data space.
Their values on the particular three inputs b_d, and
nonvanishing of (LC132), remain unproved. The nonzero
head-triplet determinant Delta does not settle that issue.

## Endpoint values and first divided jets cannot recover the head margins

The same Pro42 calculation supplies a uniform obstruction
to an endpoint-only simplification of (LC132). For a
coordinate-divisible zero-sum row define ell_i(Y) by
Y(Q_i)=ell_i(Y)v(Q_i), and define the first divided
observation nu_i(Y)=(Y_i/X_i)(Q_i). For the three
incoming columns of any one block, their three-by-three
ell-value matrix is generically invertible for every
fixed positive r.

To verify this, remove the nonzero row factors given by
the deletion-tail binary determinants and the nonzero
column factors A_t(c,0). The remaining matrix has entries
X_c(Q_i)/L_tc(Q_i) and zero diagonal. With time (u,v),
its determinant numerator after a common denominator is

\[
 N(u,v)=(k_1u-v)(1-k_0k_2v)(1-u)
       -(u-k_2v)(1-v)(1-k_0k_1u),\qquad
 N(0,v)=v(r_2+k_2r_0v).
 \tag{LC133}
\]

This polynomial is nonzero. Small positive u and generic
positive v give an admissible witness; the zero value
u=0 is used only to certify polynomial nonidentity.

For an incoming row whose completed deletion word ends
at block tau, the canceled endpoint relation (LC97)
gives nu_i=rho_tau,i ell_i, where, writing
d_ij=k_i k_j-1,

\[
 \rho_{t0}=\frac{r_1/v_t+r_2/u_t}{d_{12}},\qquad
 \rho_{t1}=\frac{u_t(k_0r_2+r_0/v_t)}{d_{02}},\qquad
 \rho_{t2}=\frac{v_t(k_0r_1+r_0/u_t)}{d_{01}} .
 \tag{LC134}
\]

These follow directly from rho_ti=sum_(j different from i)
eta_tij g_j. For m>=2 take the six incoming columns
from blocks m-1,m. Write E_t for their three-by-three
ell-value matrix, and R_t^edge=diag(rho_ti). Their
six-observation determinant factors as

\[
 \det\begin{pmatrix}
 E_{m-1}&E_m\\
 R_m^{\rm edge}E_{m-1}&R_{m-1}^{\rm edge}E_m
 \end{pmatrix}
  =\det E_{m-1}\det E_m
     \prod_i(\rho_{m-1,i}-\rho_{m,i}).
 \tag{LC135}
\]

The different terminal blocks are essential: deleting
m-1 leaves a word ending at m, while deleting m leaves
one ending at m-1. At times (u,v) and (lambda u,lambda v),

\[
 \prod_i(\rho_{m-1,i}-\rho_{m,i})
 =\frac{(\lambda-1)^3}{\lambda}
  \frac{k_0^2 r_1r_2(r_1u+r_2v)}{d_{01}d_{02}d_{12}} .
 \tag{LC136}
\]

At lambda=1 the two endpoint matrices coincide and have
a generically nonzero determinant by (LC133). Small
nonzero lambda-1 therefore gives a nonzero determinant
in (LC135), with positive time factors. The argument and
its signs were independently audited.

Thus these six incoming columns generically span all
six observations (ell_0,ell_1,ell_2,nu_0,nu_1,nu_2),
for every fixed positive r and m>=2. No nonzero linear
functional of these observations can annihilate all
incoming columns. In particular, they cannot alone
recover either nonzero head-margin functional in
(LC131). This rules out that specific shortcut; it
does not prove dependence of the paired family.

## A simpler uniform witness for the endpoint determinant

The uniform endpoint proof has a shorter alternative to
the coupled small-parameter estimates in (LC123). A local
calculation, checked by two independent audits, evaluates
the rational expression (LC120) at z_*=(3/2,1,1).
Write A=4^m, B=3^m, m>=1. Then

\[
 \widehat D_q(z_*)=
 \begin{pmatrix}0&a&a\\b&0&c\\b&c&0\end{pmatrix},
 \qquad
 a=\frac{2B}{A-1},\quad
 b=-\frac{(A+5)B+3A}{30(A-1)},\quad
 c=\frac{A-(A+6)B}{9(A-1)} .
 \tag{LC137}
\]

Consequently

\[
 \det\widehat D_q(z_*)
  =\frac{2B\bigl((A+5)B+3A\bigr)
             \bigl((A+6)B-A\bigr)}{135(A-1)^3}>0.
 \tag{LC138}
\]

Positivity follows already from A>1 and B>=3. Every
denominator in (LC120) is nonzero at z_*, so this
expression is regular and remains nonzero nearby.

The point z_* is not an admissible source specialization:
the state-zero last node lies on a coordinate edge, and
the state-one and state-two last nodes coincide. The
original transformed cancellation observations are
degenerate there. Equation (LC137) evaluates their
canceled rational extension, not an original residue
matrix at that point.

First choose a nearby positive generic z where det
widehat D_q remains nonzero, the last nodes are distinct
and away all coordinate edges, and the transformed
cancellation pivots xi_c are nonzero. The excluded
conditions are proper algebraic subsets. In particular
the limiting identity
xi_c=t_m(U+z_c)(vV_q)_j shows the needed pivot
nonvanishing on the usual geometry, with an active
component j chosen nonzero.

Fix that z before perturbing the first m time blocks
away from g. At the fixed last nodes all limiting
coordinates and old row forms are nonzero, so the
interior ordered products and cancellation ratios are
ordinarily continuous. At coordinate edges the actual
row products stay in the closed active two-state
blocks; their entries and the eta coefficients are
continuous there. Thus D_q tends to widehat D_q(z).
Small generic positive earlier-time perturbations give
det D_q nonzero and restore the full arrangement
geometry. Normalize each time vector by its first entry.

This two-stage continuity argument proves the same
uniform endpoint theorem and the rank bounds after
(LC123). It needs no simultaneous epsilon/delta order
estimates.

The actual active-block and exceptional-row identities are now checked
in SourceEndpointCoalescenceKernel.lean (nine declarations). The four
declarations in SourceEndpointCoalescenceWitness.lean define the ideal
coupling directly from actual exceptional rows and the existing endpoint
coefficients, derive (LC137), and prove (LC138) positive for every m>=1.
The cancellation ratio is explicit in these definitions; its extraction
from generic pole ratios and the ordered perturbation argument above
remain paper mathematics. In particular, the formal witness is not an
admissible original-source fixture. The updated cached aggregate checks
502 declarations across 46 modules, using only foundational axioms,
in 21.71 seconds with peak RSS 2,429,435,904 bytes.
The final three paired directions per sector and
the retained-old-source determinant remain open.

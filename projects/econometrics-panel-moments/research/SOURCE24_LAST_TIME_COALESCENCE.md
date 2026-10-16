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
controls F_e, which is a different map. No induction closing that
gap has been proved. These two stripping observations and their
limitations were independently checked.

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

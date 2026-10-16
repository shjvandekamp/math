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

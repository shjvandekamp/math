# Fixed cyclic matching pivots and the reduced raw quotient

**Status: independently audited paper results; not Lean formalized.**
The [Pro13 investigation](https://chatgpt.com/c/6ad14765-2430-83eb-bd5d-a810e0a3f486)
proposed the fixed cyclic minor and the coupled elimination below. The
primary researcher and the independent deletion-induction reviewer checked
the source normalization, asymptotic coefficients, determinant, and block
reduction. The remaining reduced matrix is not proved to have full rank.

This sharpens the generic matching-map result in
[`SOURCE24_RAW_QUOTIENT.md`](SOURCE24_RAW_QUOTIENT.md): one specified set of
3q incoming columns already supplies matching pivots for every fixed q>=2.
It also removes those pivots and six row-sum pivots from the full boundary
problem without adding ranks of overlapping observation groups.

## Actual words and matching normalization

Number the old blocks 1,...,q and write N=q+1 for the new block. States
are 0,1,2. With row-vector conventions, set

\[
 A_t=G\operatorname{diag}(f_{t0},f_{t1},f_{t2}),\qquad
 L_{ta}=\sum_i A_t(a,i)X_i,\qquad
 K_t(a,i)=\frac{A_t(a,i)X_i}{L_{ta}},
 \qquad f_t=(1,u_t,v_t).
 \tag{MP1}
\]

For distinct t,s in {1,...,q,N}, the actual completed raw row is

\[
 \widehat Q_{t,s,a,b}
 =X_a K_t(a,b)e_b K_s
   \prod_{j\in\{1,\ldots,q,N\}\setminus\{t,s\}}^{\uparrow}K_j.
 \tag{MP2}
\]

The arrow means increasing block order. Define the incoming and outgoing
boundary columns by

\[
 I_t^{ab}=\widehat Q_{t,N,a,b},\qquad
 O_t^{ab}=\widehat Q_{N,t,a,b},\qquad 1\le t\le q.
 \tag{MP3}
\]

There are 18q such columns. For any row H, write
B_H=H diag(X)^-1. The matching functional is exactly RQ4:

\[
 \eta_{sd}(H)=
 \left[\left(\frac{\operatorname{Res}_{L_{sd}}B_H}{X_d}\right)
                  A_N^{-1}\right]_d\bigg|_{L_{sd}=X_d=0}.
 \tag{MP4}
\]

Here Res_L means multiplication by L followed by restriction to L=0.
The departure factor X_d is cancelled before evaluating the matching
point. No extra row or column scale is inserted in MP4.

Let b(a)=a+1 and c(a)=a+2 modulo 3. The selected incoming columns are

\[
 Z_{ta}=I_t^{a,b(a)},\qquad
 J_q=\bigl(\eta_{sd}(Z_{ta})\bigr)_{(s,d),(t,a)}.
 \tag{MP5}
\]

Both rows and columns of J_q are ordered first by old block, then by
state 0,1,2. The claim is that this particular 3q-by-3q determinant is
generically nonzero for every fixed q>=2.

## A positive perturbation with the required row normalization

Start with the common matrix

\[
 \widetilde G_\varepsilon(i,j)=
 \begin{cases}1,&i=j,\\\varepsilon,&i\ne j,\end{cases}
 \qquad \varepsilon>0.
 \tag{MP6}
\]

Multiplying its rows by diag(1,epsilon^-1,epsilon^-1) produces a positive
common G whose first column is 1, as required by the model. This common
row scaling preserves every K_t and every matching functional. Indeed,
under A_t'=S A_t, the line L_ta and its residue scale by S_aa, while
A_N'^-1=A_N^-1 S^-1 scales its output-a column by S_aa^-1. These factors
cancel in MP4. We may therefore calculate using the unnormalized
\(\widetilde G_\varepsilon\).

Choose f_N=(1,1,1), and take the last two old factors to be

\[
 f_{q-1}=(1,2,3),\qquad f_q=(1,4,5).
 \tag{MP7}
\]

The earlier factors are generic positive (1,u_t,v_t). On the matching
axis X_d=0, its point equation is

\[
 \sum_{i\ne d}f_{si}X_i=0.
 \tag{MP8}
\]

It is independent of epsilon after cancelling the common epsilon factor.
The two active coordinates are nonzero. Choose the earlier factors to
avoid collisions of the matching denominators. The calculations below
are regular rational expansions at these fixed points as epsilon tends
to zero through positive values.

For an active state i different from d, each block j satisfies

\[
 K_j\big|_{\{0,1,2\}\setminus\{d\}}=I+O(\varepsilon),
 \qquad
 \frac{K_j(i,d)}{X_d}
   =\varepsilon\frac{f_{jd}}{f_{ji}X_i}+O(\varepsilon^2).
 \tag{MP9}
\]

The second expression is cancelled before setting X_d=0. At the final
old factor ell, the stripped active-to-departure entry is

\[
 \frac{(A_\ell A_N^{-1})_{id}}{L_{\ell i}}
 =\varepsilon\frac{f_{\ell d}-f_{\ell i}}
                         {f_{\ell i}X_i}+O(\varepsilon^2),
 \qquad i\ne d.
 \tag{MP10}
\]

Both statements follow by expanding \(\widetilde G_\varepsilon\) about
the identity. In particular, the off-diagonal entry of
A_ell A_N^-1 has first coefficient f_ell,d-f_ell,i.

## The leading matching matrix

The conjugated matrices

\[
 \mathcal J_j=\operatorname{diag}(X/L_j)A_j
            =\operatorname{diag}(X)K_j\operatorname{diag}(X)^{-1}
\]

make the cancellation in MP4 explicit. For I_t^(ab), its B-row is

\[
 B_{I_t^{ab}}=\frac{X_aA_t(a,b)}{L_{ta}}
                  e_b\mathcal J_N
                  \prod_{j\in\{1,\ldots,q\}\setminus\{t\}}^{\uparrow}
                  \mathcal J_j.
 \tag{MP11}
\]

All products in the next two formulas are over old blocks 1,...,q.
At its own old line s=t, only d=a contributes, and removing the matching
factor gives

\[
 \eta_{ta}(I_t^{ab})=
 A_t(a,b)e_b\mathcal J_N
 \prod_{j\ne t}^{\uparrow}\mathcal J_j A_N^{-1}e_a
 \bigg|_{L_{ta}=X_a=0}.
 \tag{MP12}
\]

If s!=t, split the ascending old word into the blocks before s and
after s, with t omitted. Then the same divided residue is

\[
 \eta_{sd}(I_t^{ab})=
 \frac{X_aA_t(a,b)}{L_{ta}}
 \biggl[e_b\mathcal J_N\prod_{j<s,\ j\ne t}^{\uparrow}
                      \mathcal J_j e_d\biggr]
 \biggl[A_s(d,:)\prod_{j>s,\ j\ne t}^{\uparrow}
                      \mathcal J_j A_N^{-1}e_d\biggr]
 \bigg|_{L_{sd}=X_d=0}.
 \tag{MP13}
\]

Thus a cyclic column Z_ta can have support only at its own row (t,a)
and at rows (s,c(a)) with s!=t. At another row with d=a, its prefix
X_a vanishes. At another row with d=b(a), row b(a) of restricted
\(\mathcal J_N\) is zero.

Let ell(t) be the largest old block other than t. Let j_t be its actual
predecessor in the word consisting of N followed by the ascending old
blocks other than t. In particular, for q=2 this predecessor is N for
both choices of t; one must retain f_N=(1,1,1) in the formulas.

Equations MP9--MP13 give the own-row coefficient

\[
 \eta_{ta}(Z_{ta})=\varepsilon^2 d_{ta}+O(\varepsilon^3),
 \qquad
 d_{ta}=\frac{f_{t,b(a)}}{f_{\ell(t),b(a)}}
              \bigl(f_{\ell(t),a}-f_{\ell(t),b(a)}\bigr).
 \tag{MP14}
\]

For s different from both t and ell(t), the cross-row coefficient is
O(epsilon^4). Its prefix is O(epsilon), the transition into the
residue state before s is O(epsilon), the active part of the residue
row is O(epsilon), and the last stripped active-to-departure entry is
O(epsilon). The residue state's diagonal part is killed by the following
restricted conjugated factor.

The terminal residue s=ell(t) is different: there is no following old
factor, and its stripped diagonal entry has order one. Consequently,

\[
 \eta_{\ell(t),c(a)}(Z_{ta})
   =\varepsilon^2 e_{ta}+O(\varepsilon^3),\qquad
 e_{ta}=\frac{f_{t,b(a)}}{f_{ta}}
         \frac{f_{j_t,c(a)}}{f_{j_t,b(a)}}f_{\ell(t),c(a)}.
 \tag{MP15}
\]

The predecessor j_t is essential here. In a restricted conjugated word,
entering the deleted state before the last factor is killed by the next
zero departure row; the entry into that state is therefore contributed
by the actual immediately preceding factor. This also explains why the
terminal O(epsilon^2) contribution cannot be estimated as a nonterminal
O(epsilon^4) contribution.

## A fixed determinant for every q>=2

Set

\[
 \pi_t=u_tv_t=\prod_a f_{ta},\qquad
 \Delta_t=(f_{t0}-f_{t1})(f_{t1}-f_{t2})(f_{t2}-f_{t0}).
 \tag{MP16}
\]

After removing epsilon^2 from every column of J_q, its leading matrix
has a diagonal block for each of the first q-2 old blocks. The only
additional leading entries from these columns lie in the final block q.
The last six rows and columns form a diagonal matrix plus one six-cycle:
the cross entry sends (q-1,a) to (q,c(a)), and (q,a) to (q-1,c(a)).

For an early block t, multiplying MP14 over the three states gives
(pi_t/pi_q)Delta_q. For the final two blocks the product of all six
diagonal entries is Delta_(q-1)Delta_q. Multiplying MP15 over the three
states cancels both cyclic ratios, so the product around the six-cycle
is pi_(q-1)pi_q. A six-cycle has negative permutation sign. Hence the
leading determinant is

\[
 \left(\prod_{t=1}^{q-2}\frac{\pi_t}{\pi_q}\Delta_q\right)
 \bigl(\Delta_{q-1}\Delta_q-\pi_{q-1}\pi_q\bigr).
 \tag{MP17}
\]

For MP7, pi_(q-1)=6, Delta_(q-1)=2, pi_q=20 and Delta_q=12. Therefore

\[
 \det J_q
 =-96\left(\frac35\right)^{q-2}
      \left(\prod_{t=1}^{q-2}u_tv_t\right)\varepsilon^{6q}
      +O(\varepsilon^{6q+1})\ne0
 \tag{MP18}
\]

for all sufficiently small positive epsilon. When q=2 the early product
is empty, j_t=N, and the same formula gives coefficient -96.

For each fixed q, this gives a positive common-G nonvanishing witness
after the row normalization following MP6. All entries are rational in
the model parameters. Clearing denominators therefore proves that the
specified cyclic matching minor is not identically zero. Its nonvanishing
can be combined with the required generic geometric conditions. This is
a generic result for each fixed finite horizon, not one fixed open set
asserted to work simultaneously for unbounded q.

## Eliminate matching and row-sum pivots together

Work over the parameter function field \(\mathbb K\), or at a specialization
where the displayed denominators and det J_q are nonzero.

For a boundary coefficient vector, denote its outgoing coefficients by
alpha_out,t^(ab). On a new line L_Nc=0, the row-sum residue divided by
X_c is

\[
 \sum_{b=0}^2 A_N(c,b)X_b\sum_{t=1}^q\alpha_{\mathrm{out},t}^{cb}
 =\sum_{k=1}^2 A_N(c,k)X_k S_{ck},\qquad
 S_{ck}=\sum_{t=1}^q
   \bigl(\alpha_{\mathrm{out},t}^{ck}
             -\alpha_{\mathrm{out},t}^{c0}\bigr).
 \tag{MP19}
\]

The equality uses L_Nc=0. These are the six normalized row-sum tests
from RQ3. They vanish on all incoming columns because the row sum of
I_t^(ab) is X_a K_t(a,b), with no new-line denominator.

Choose six outgoing columns

\[
 C_{ck}=O_q^{ck},\qquad c=0,1,2,\quad k=1,2.
 \tag{MP20}
\]

Let \(\mathcal C\) be this column matrix, \(\mathcal Z\) the 3q columns
MP5, and \(\mathcal B\) the remaining 15q-6 boundary columns. With
matching orders for the six rows and columns,

\[
 S(\mathcal C)=I_6,\qquad S(\mathcal Z)=0,\qquad
 \eta(\mathcal Z)=J_q.
\]

On the open set det J_q!=0, form the actual corrected columns

\[
 \mathcal B_0=\mathcal B-\mathcal C S(\mathcal B),\qquad
 \mathcal B^\sharp=\mathcal B_0
       -\mathcal ZJ_q^{-1}\eta(\mathcal B_0).
 \tag{MP21}
\]

Both S and eta vanish on \(\mathcal B^\sharp\). The first subtraction
must precede the second: \(\eta(\mathcal C)\) need not vanish.

Let U collect the remaining quotient observations from RQ5: the 9q
new/old intersection coordinates and the 6q+3 axis coordinates. Thus

\[
 R_q=U(\mathcal B^\sharp)
       \in\mathbb K^{(15q+3)\times(15q-6)}.
 \tag{MP22}
\]

For completeness, also put
\(\mathcal C^\sharp=\mathcal C-\mathcal ZJ_q^{-1}\eta(\mathcal C)\).
The invertible column replacement
(\(\mathcal Z,\mathcal C,\mathcal B\)) to
(\(\mathcal Z,\mathcal C^\sharp,\mathcal B^\sharp\)) transforms the
complete test matrix T_N=(eta,S,U) to

\[
 \begin{pmatrix}
 J_q&0&0\\
 0&I_6&0\\
 U(\mathcal Z)&U(\mathcal C^\sharp)&R_q
 \end{pmatrix}.
 \tag{MP23}
\]

Eliminating the bottom entries in the first two column blocks gives the
exact coupled rank identity

\[
 \operatorname{rank}T_N(\widehat Q_\partial)
       =3q+6+\operatorname{rank}R_q.
 \tag{MP24}
\]

Consequently, the full boundary criterion is equivalent to
rank R_q=15q-6. This remaining rank is open; matching surjectivity alone
does not establish it.

For any set I of 15q-6 rows of U, the corresponding square reduced
minor has the exact bordered expression

\[
 \det (R_q)_I
 =\frac{\displaystyle
  \det\begin{pmatrix}
    J_q&\eta(\mathcal B_0)\\
    U_I(\mathcal Z)&U_I(\mathcal B_0)
  \end{pmatrix}}
  {\det J_q}.
 \tag{MP25}
\]

One candidate square row set consists of every axis row and every
new/old intersection row except the nine incident to old block q.
Its size is (6q+3)+(9q-9)=15q-6. This specifies a concrete candidate
minor only: no nonvanishing claim is made for that minor or for another
maximal minor of R_q.

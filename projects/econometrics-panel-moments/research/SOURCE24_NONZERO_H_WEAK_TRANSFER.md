# Separation of the weak layers at nonzero h

Status: independently audited paper proof, not a Lean theorem. For generic
nonzero \(h\), this proves independence of the \(3(m-2)\) promoted weak
directions originating at lengths \(3,\ldots,m\). The endpoint extension
below includes all four old weak directions from the checked two-block
base. Their accumulated function rank is \(3m-2\); the justified weak
residue rank is at least \(3m-3\), because constant functions are invisible
to those residues. The full paired determinant and Eq. (24) remain open.

The actual binary lifting theorem is
(SL28)--(SL35) of
[SOURCE24_SCALAR_LAURENT_SPANNING.md](SOURCE24_SCALAR_LAURENT_SPANNING.md).
The corresponding boundary calculation is
[SOURCE24_BINARY_WEAK_TRANSFER.md](SOURCE24_BINARY_WEAK_TRANSFER.md).
The distinction from that calculation is essential: the evaluation at
\(r=2h\) below is nonzero when \(h\ne0\), but vanishes at \(h=0\).

## Actual columns and the new first weak image

Fix

\[
 G=\begin{pmatrix}2&1&1\\1&2&1\\1&1&2\end{pmatrix},\quad
 X=(1,-r,r-2h),\quad v=(2h,-r,r-2h),\quad
 A_t=G\operatorname{diag}(1,a_t,b_t\delta),\quad
 K_t=\operatorname{diag}(A_tX)^{-1}A_t\operatorname{diag}X.
 \tag{NH1}
\]

Use distinct \(a_t\in(1,2)\), positive \(b_t\), and generic sufficiently
small positive \(h\). The old binary nodes are \(2/a_t,1/(2a_t),1/a_t\).
They are distinct, and \(2h\) is assumed to avoid them. Every coefficient
combination is constant in \(r\). Formal order-raising combinations may
depend on \(\delta\); their coefficients lie in the rational parameter
field, including \(h\).

The ordered completed columns are

\[
 \begin{split}
 C^H_{sb}&=X_be_bP_s,&P_s&=K_sK_1\cdots\widehat K_s\cdots K_k,\\
 C^J_{tc}&=\mu_{tc}vP^t,&P^t&=K_1\cdots\widehat K_t\cdots K_k,\\
 (\mu_{t0},\mu_{t1},\mu_{t2})
 &=\left(2/L_{t0},-r/L_{t1},(r-2h)/L_{t2}\right),
 &L_{tc}&=(A_tX)_c.
 \end{split}
 \tag{NH2}
\]

The actual paired rows are \(H_{sb}=X_be_b-C^H_{sb}\) and
\(J_{tc}=-C^J_{tc}\). Thus the completed signs in (NH2) are explicit;
the polynomial heads remain in the actual source combinations.

At \(\delta=0\), put

\[
 \begin{split}
 l_{t0}&=2-a_tr,&l_{t1}&=1-2a_tr,&l_{t2}&=1-a_tr,\\
 d_t&=\frac{-3a_tr}{l_{t0}l_{t1}},&
 e_t&=\frac{-a_tr}{l_{t0}l_{t2}},&D_m&=\prod_{t\le m}d_t,\\
 Q_{t,h}&=-r+(r-2h)e_t/d_t
 =\frac{a_tr^2+(4a_th-2)r-2h}{3(1-a_tr)},&&
 \mathcal A_t&=\frac{1+a_tr}{3a_tr}.
 \end{split}
 \tag{NH3}
\]

For a zero-sum row \(q\), \((qK_t^0)_1=d_tq_1+e_tq_2\).
The old binary lifting theorem supplies an actual exact-row-sum-zero
completed lift of every rational function with simple old poles,
bounded at infinity and zero at zero. The head sum used in its
continuation is \(2hC^H_{s0}+C^H_{s1}+C^H_{s2}\), whose row sum
vanishes identically, not just at \(h=0\).

Let \(k=m+1\ge3\), \(A=a_k\), \(a=a_1\), \(\xi=1/A\),
\(Q=Q_{1,h}\), and
\(\Delta_k=b_k\mathcal A_k-b_m\mathcal A_m\). Use the three terminal
combinations

\[
 E_0=C^J_{k0},\qquad E_1=C^J_{k1},\qquad
 E_2=2hC^H_{k0}+C^H_{k1}+C^H_{k2}
                         +Q(\xi)^{-1}C^J_{k2}.
 \tag{NH4}
\]

They have exact zero row sum. Their binary first outputs are
\(B_j=D_m\beta_j\), where

\[
 \beta_0=\frac{2Q}{2-Ar},\qquad
 \beta_1=\frac{-rQ}{1-2Ar},\qquad
 \beta_2=d_kQ_{k,h}
                +\frac{(r-2h)Q}{Q(\xi)(1-Ar)}.
 \tag{NH5}
\]

The new state-2 pole of \(\beta_2\) cancels. Unlike its \(h=0\)
specialization, it generally has both new state-0 and state-1 poles:

\[
 d_kQ_{k,h}
 =\frac{Ar^2}{(1-2Ar)(1-Ar)}
       +\frac{2Ah r}{(2-Ar)(1-Ar)}.
 \tag{NH6}
\]

Each \(-B_j/d_k\) is an old admissible binary scalar: it has only
simple old poles, is \(O(r^{m-1})\) at zero, and
\(O(r^{2-m})\) at infinity. Choose an actual shorter lift
\(\mathcal C_{-B_j/d_k}\) and set

\[
 Y_j=E_j+\mathcal C_{-B_j/d_k}K_k.
 \tag{NH7}
\]

These completed rows have exact row sum zero and zero binary limit.
The exact last-kernel identity, divided by \(X_2=r-2h\), gives for
a word with a nonempty prefix and last index \(l\)

\[
 \left.\frac{C_2}{\delta(r-2h)}\right|_0
       =\frac{b_l}{3}(C\mathbf1)
                         -b_l\mathcal A_l(C|_0)_1.
\]

Every word in (NH4) ends in \(m\), while its correcting inherited
word ends in \(k\). The prefix is nonempty since \(m\ge2\).
Consequently the first weak image of these actual vectors is

\[
 \mathcal N_k(h)=\Delta_kD_m
                    \operatorname{span}\{\beta_0,\beta_1,\beta_2\}.
 \tag{NH8}
\]

Its functions vanish at zero and infinity and are regular at \(2h\).
Their independence is proved below, without an extrapolation from \(h=0\).

## The actual next-layer transfer

Suppose an actual completed row has exact row sum zero and
\(C=\delta^s q+O(\delta^{s+1})\), \(s\ge1\). Write
\(q_2=(r-2h)c\). Assume that \(c\) has only simple old poles,
\(c(0)=c(\infty)=0\), and is regular at \(r=2h\).
The coordinate factor in an actual completed output makes this last
regularity an actual source condition.

After appending \(K_k\), the leading binary error is
\(g=d_kq_1+e_k(r-2h)c\). The correct first inherited scalar lift is

\[
 q_1+rc=-q_0+2hc.
 \tag{NH9}
\]

It is bounded at infinity and zero at zero. Here \(q_0\) is bounded
at infinity by the final old kernel's output-0 factor, and \(q_1(0)=0\)
by its coordinate factor. Using \(q_1+q_2\) instead would omit the
\(2hc\) term. After subtracting the appended lift of (NH9), the
remaining binary error is precisely \(d_kQ_{k,h}c\).

Put \(\lambda=c(\xi)/D_m(\xi)\). Its lift consists of the terminal
combination \(\lambda(2hC^H_{k0}+C^H_{k1}+C^H_{k2})\), together
with an appended shorter lift of
\(Q_{k,h}(c-\lambda D_m)\). The new state-2 pole cancels; this
shorter scalar is bounded at infinity and zero at zero.
Subtracting \(\delta^s\) times the complete binary lift raises the
completed-row order by one. Its next weak coefficient is exactly

\[
 \boxed{\mathscr T_{k,h}(c)
 =\chi_{k,h}c
      -\Delta_k\frac{c(\xi)}{D_m(\xi)}D_md_kQ_{k,h},\qquad
 \chi_{k,h}=\frac{4b_k(r-2h)}{3(1-Ar)}.}
 \tag{NH10}
\]

This follows by canceling the common last-kernel first-output term;
only the terminal lift's different last index contributes the second
term. Unknown higher coefficients of \(C\) do not enter: their
contribution contains \(K_k^0e_2=0\). The same actual coefficients
are used in all three outputs.

The formula preserves the stated scalar domain. At zero its second
term is \(O(r^m)\), and its first term vanishes. At infinity both
terms vanish. Only simple old or new poles occur, and every term is
regular at \(2h\). Different choices of binary lift change the
weak coefficient by a member of \(\mathcal N_k(h)\).

## A coordinate evaluation kills the exceptional kernel

Assume the following generic units in addition to the distinct nodes:

\[
 \begin{gathered}
 Q(\xi)Q(2/A)Q(1/(2A))\ne0,\qquad
 \Delta_k(2/A)\Delta_k(1/(2A))\Delta_k(2h)\ne0,\\
 \xi\ne2h,\qquad 4b_k/3+\Delta_k(\xi)\ne0.
 \end{gathered}
 \tag{NH11}
\]

All old denominators at these new points are units. The value \(2h\)
also avoids zero and every new node. These conditions hold on a
nonempty generic positive open set: first choose distinct \(a_t\),
then sufficiently small nonzero \(h\), and avoid the finitely many
nonzero equations in the positive \(b_t\).

If \(\mathscr T_{k,h}(c)\in\mathcal N_k(h)\), its new state-2 pole
must vanish. Multiplication by \(1-Ar\), followed by evaluation at
\(\xi\), gives

\[
 (\xi-2h)\left(\frac{4b_k}{3}+\Delta_k(\xi)\right)c(\xi).
\]

Thus \(c(\xi)=0\), and (NH10) reduces to \(\chi_{k,h}c\).
It has no new state-0 or state-1 pole. In the span in (NH8), canceling
those two poles leaves exactly the line generated by

\[
 \overline\beta
 =\beta_2+\frac{2h}{Q(2/A)}\beta_0
                      +\frac1{Q(1/(2A))}\beta_1.
 \tag{NH12}
\]

Indeed \(\beta_0\) has only the new state-0 pole and \(\beta_1\)
only the new state-1 pole, with nonzero coefficients. Formula (NH6)
gives the displayed cancellation constants.

Define

\[
 N_0=2(a-A)+Ah(4a-A),\qquad
 N_1=a-4A+8Ah(a-A).
\]

Direct evaluation gives the crucial nonzero value

\[
 \boxed{\overline\beta(2h)
 =-\frac{6Ah^2(4a^2-5aA+4A^2)}{N_0N_1}.}
 \tag{NH13}
\]

For an explicit algebra check,
\(Q(2/A)=2N_0/[3A(A-2a)]\) and
\(Q(1/(2A))=N_1/[6A(2A-a)]\). Substituting these into

\[
 \overline\beta(2h)
 =\frac{6Ah^2}{(1-Ah)(1-4Ah)}
  -\frac{4h^2}{(1-Ah)Q(2/A)}
  +\frac{4h^2}{(1-4Ah)Q(1/(2A))}
\]

leaves the numerator identity

\[
 \begin{split}
 &N_0N_1-(A-2a)(1-4Ah)N_1
                  +4(2A-a)(1-Ah)N_0\\
 &\hspace{1cm}=-(1-Ah)(1-4Ah)(4a^2-5aA+4A^2).
 \end{split}
\]

The quadratic equals \(4(a-A)^2+3aA>0\) for positive \(a,A\).
Therefore (NH13) is nonzero under the stated units and \(h\ne0\).
It also proves \(\dim\mathcal N_k(h)=3\).

The displayed polynomial factorization, its positive quadratic factor,
and the reduced scalar's nonvanishing are now checked in
[SourceWeakTransferInterpolation.lean](../formal/PanelMoments/SourceWeakTransferInterpolation.lean).
That module contains eight scalar theorems with explicit denominator
hypotheses. It does not identify an actual source row or formalize the
transfer and rank arguments in this note.

On the other hand, \(\chi_{k,h}c\) vanishes at \(r=2h\), because
\(c\) is regular there. Since \(\Delta_k(2h)D_m(2h)\ne0\), no
nonzero multiple of the remaining line in (NH12) can equal it.
Hence the multiple is zero, then \(c=0\). We have proved

\[
 \boxed{\ker(\mathscr T_{k,h}\bmod\mathcal N_k(h))=0}
 \tag{NH14}
\]

on the stated endpoint-zero domain. The one-dimensional boundary
kernel from (BW23) consequently does not persist at generic nonzero \(h\).

## Exact scalar decomposition and actual graded consequences

Let \(\mathcal E_m(h)\) be the space of rational functions with
simple poles only at the \(3m\) old nodes and values zero at both zero
and infinity. Since \(2h\) is off those nodes, regularity there is
automatic. Its dimension is \(3m-1\): a proper rational function has
\(3m\) independent simple-pole coefficients, with one condition at zero.
The domain preservation and (NH14) therefore give the exact scalar
direct sum

\[
 \boxed{\mathcal E_{m+1}(h)
      =\mathcal N_{m+1}(h)
                    \oplus\mathscr T_{m+1,h}\mathcal E_m(h).}
 \tag{NH15}
\]

The dimension check is \(3+(3m-1)=3(m+1)-1\). This ambient equality
does not assert that every member is supplied by an old actual source.
Its actual realization here is the explicit construction above on
columns that are supplied by actual sources.

Start with the three vectors (NH7) at length three. At every append,
promote the inherited vectors by the actual binary correction in
(NH9)--(NH10), and add the three new vectors (NH7). Every weak
coefficient lies in \(\mathcal E_m(h)\). Induction using (NH14) proves
that their accumulated weak coefficients are independent, with

\[
 \boxed{\dim\mathcal S_m^{\rm later}(h)=3(m-2),\qquad m\ge3.}
 \tag{NH16}
\]

The different origins have different formal orders: a vector born at
length \(n\) has completed order at least \(\delta^{m-n+1}\) after
promotion to length \(m\). Its first weak coefficient is the iterated
transfer specified above. Independence means independence after these
specified column factors are removed, not an addition of unrelated
unscaled ranks.

The checked actual two-block base in
[SOURCE24_BINARY_TWO_BLOCK_BASE.md](SOURCE24_BINARY_TWO_BLOCK_BASE.md)
gives a further consequence. Its invertible normalized residue matrix
is injective on the four-dimensional exact completed binary kernel,
where the upper observations vanish. Thus the weak map on that kernel
has rank four at the displayed boundary base, and hence generically in
\(h\) and the table parameters. Its four-dimensional weak-function image
consists of \(c\)'s regular at \(2h\), finite at zero, and bounded at
infinity. The kernel of the two endpoint values \((c(0),c(\infty))\)
has dimension at least two. Choose two independent actual vectors in
that kernel and promote them by the same construction. Equation (NH14)
then yields

\[
 \boxed{\dim\mathcal S_m^{\rm selected}(h)\ge
                         2+3(m-2)=3m-4.}
 \tag{NH17}
\]

This uses the checked base, not an assumption of full paired independence
at later lengths. The endpoint-kernel basis and the correcting sections
are taken over the generic parameter field containing \(h\); they may
have poles at \(h=0\). No regular normalization at that boundary is
claimed.

These weak functions also remain independent under the actual residue
observations. For \(c\in\mathcal E_m(h)\), the function
\((r-2h)c\) is bounded at infinity and vanishes at \(2h\).
If all its simple-pole residues vanish, it is a constant polynomial;
that value at \(2h\) makes the constant zero. Thus the weak residue
map is injective on this space. The promoted columns have leading
upper output zero after their prescribed factors are removed, whereas
the actual binary lifting theorem supplies \(3m\) upper residue pivots.
Consequently (NH17) constructs a graded subsystem of rank at least
\(6m-4\).

At this stage, four directions remain outside the construction, associated
with the two possible old endpoint values and the two polynomial head gauges.
This is a structural reduction of the graded problem. The previously
proved raw paired rank bound \(6m-3\) is numerically stronger; the new
content is separation of these actual promoted weak layers. Neither
bound proves the full determinant nonzero, determines its order along
\(h=\epsilon,\delta=\epsilon^2\), or proves independence in Eq. (24).

## Actual corrections for both endpoint values

The preceding endpoint-zero construction extends to every bounded old
scalar \(c\), without changing the original source family. Define the
actual exact-row-sum-zero head differences

\[
 \mathcal H_{k,b}=C^H_{kb}-C^H_{1b},\qquad b=0,1,
 \qquad F_b=(\mathcal H_{k,b}|_0)_1,\qquad
 B_{{\rm new},b}=(C^H_{kb}|_0)_1.
 \tag{NH18}
\]

The binary determinant of a moved-first word is independent of its
order. Hence \(F_1=-rF_0\). The Laurent extremes from the binary
lifting proof give

\[
 \begin{array}{c|cc}
 &r=0&r\longrightarrow\infty\\ \hline
 F_0/d_k&(a_m-A)/(3A)&(a_m-A)/(3a_m)+O(r^{-1})\\
 F_1/d_k&O(r)&(A-a_m)r/(3a_m)+O(1).
 \end{array}
 \tag{NH19}
\]

These quotients have only old poles; neither has a new state-2 pole.
Let \(c_0=c(0)\), \(c_\infty=c(\infty)\), and set

\[
 \begin{split}
 \alpha_0&=\frac{2hA}{A-a_m}c_0,&
 \alpha_\infty&=-\frac{a_m}{A-a_m}c_\infty,&
 \lambda&=\frac{c(\xi)}{D_m(\xi)},\\
 f&=Q_{k,h}(c-\lambda D_m)
             -\alpha_0F_0/d_k-\alpha_\infty F_1/d_k.
 \end{split}
 \tag{NH20}
\]

The value \(Q_{k,h}(0)=-2h/3\), the linear coefficient
\(Q_{k,h}=-r/3+O(1)\) at infinity, and (NH19) show that \(f\)
vanishes at zero and is bounded at infinity. Its new state-2 pole is
canceled by \(\lambda\). It therefore has an actual old binary lift.
The first inherited lift remains (NH9): even for nonzero endpoint
values, \(q_1+rc=-q_0+2hc\) is bounded at infinity and zero at zero.

Write \(Z_k(h)=2hC^H_{k0}+C^H_{k1}+C^H_{k2}\).
Use the terminal lifts \(\lambda Z_k(h)\),
\(\alpha_0\mathcal H_{k,0}\), and
\(\alpha_\infty\mathcal H_{k,1}\), together with the appended old
lift of \(f\). The weak defects of the two head differences, relative
to words ending in \(k\), are

\[
 W_0=\Delta_k B_{{\rm new},0}+\frac{b_m-b_k}{3},\qquad
 W_1=\Delta_k B_{{\rm new},1}+\frac{b_k-b_m}{3}r.
 \tag{NH21}
\]

The polynomial terms are essential. In general the defect of
\(\mathcal H_{k,b}\) is
\(\Delta_kB_{{\rm new},b}+(b_m-b_k)X_b/3\), since its two
constituents have equal row sum \(X_b\), but different last indices.

The endpoint values needed below are

\[
 \begin{split}
 W_0(0)&=\frac{b_m}{2}-\frac{b_k}{3}-\frac{a_mb_k}{6A},&
 W_0(\infty)&=0,\\
 W_1(0)&=0,&
 W_1(\infty)&=\frac{b_m}{2a_m}-\frac{b_k}{6a_m}-\frac{b_k}{3A}.
 \end{split}
 \tag{NH22}
\]

For example, \(B_{{\rm new},0}=-a_mr/2+O(r^2)\) at zero and
\(B_{{\rm new},0}\to1\) at infinity, proving the first row.
The second row is the actual terminal-order calculation (BW27)--(BW29).
All these binary functions are independent of \(h\); the coordinate
factor \(r-2h\) was divided out before their weak coefficients were
taken.

The exact full transfer is consequently

\[
 \boxed{\mathscr T^{\rm full}_{k,h}(c)
  =\chi_{k,h}c-\Delta_k\lambda D_md_kQ_{k,h}
                    -\alpha_0W_0-\alpha_\infty W_1.}
 \tag{NH23}
\]

It has simple old and new poles, is regular at \(2h\), and is bounded
at infinity. Its endpoint map is diagonal:

\[
 \begin{split}
 \mathscr T^{\rm full}_{k,h}(c)(0)&=\kappa_0c_0,&
 \kappa_0&=h\frac{(3a_m-2A)b_k-A b_m}{A-a_m},\\
 \mathscr T^{\rm full}_{k,h}(c)(\infty)&=\kappa_\infty c_\infty,&
 \kappa_\infty&=\frac{A b_m-(3A-2a_m)b_k}{2A(A-a_m)}.
 \end{split}
 \tag{NH24}
\]

The cross terms vanish because \(W_1(0)=W_0(\infty)=0\).
These two endpoint multipliers are simultaneously nonzero generically.
For instance \(b_k=b_m=\beta>0\) gives
\(\kappa_0=-3h\beta\) and \(\kappa_\infty=-\beta/A\).
Intersect these nonzero conditions with (NH11).

Since every member of \(\mathcal N_k(h)\) has both endpoint values
zero, membership of \(\mathscr T^{\rm full}_{k,h}(c)\) in that image
forces \(c_0=c_\infty=0\). Then (NH23) reduces to (NH10), and
(NH14) forces \(c=0\). Let \(\mathcal F_m\) denote all bounded
rational functions with simple poles at the old \(3m\) nodes.
It has dimension \(3m+1\), and regularity at \(2h\) is automatic.
We have proved

\[
 \boxed{\begin{split}
 \ker(\mathscr T^{\rm full}_{k,h}\bmod\mathcal N_k(h))&=0,\\
 \mathcal F_{m+1}
   &=\mathcal N_{m+1}(h)
       \oplus\mathscr T^{\rm full}_{m+1,h}\mathcal F_m.
 \end{split}}
 \tag{NH25}
\]

The direct-sum equality uses \(3+(3m+1)=3(m+1)+1\), together
with the proved membership and injectivity, not dimension alone.
The proper subspace \(c(\infty)=0\) is preserved by the same map.

## All four old weak functions, and the remaining residue ambiguity

Start with all four independent actual weak functions from the
two-block base. They belong to \(\mathcal F_2\). Apply the actual
corrections (NH18)--(NH23) at every subsequent append and add the
three new vectors (NH7). Quotient injectivity in (NH25) gives

\[
 \boxed{\dim\mathcal S_m^{\rm full\ weak}(h)
                   =4+3(m-2)=3m-2.}
 \tag{NH26}
\]

This is independence of actual weak functions after their prescribed
formal column factors. It is not yet the same rank for the weak
residue observations.

Indeed the residue map on \(\mathcal F_m\) has the precise kernel

\[
 \ker\{c\longmapsto
          (\operatorname{Res}_{\rm old\ nodes}(r-2h)c)\}
                    =\operatorname{span}\{1\}.
 \tag{NH27}
\]

To prove it, a function with zero residues has
\((r-2h)c\) polynomial of degree at most one, since \(c\) is bounded
at infinity. Regularity of \(c\) at \(2h\) forces this polynomial
to vanish there. It is therefore a constant multiple of \(r-2h\),
so \(c\) is constant. Conversely constants plainly have zero residues.

The full function rank (NH26) consequently gives weak residue rank
at least \(3m-3\). One can obtain that bound without any quotient
ambiguity: select three independent proper functions from the
four-dimensional two-block image, which is possible because
\(c\mapsto c(\infty)\) has rank at most one. Equation (NH24)
preserves properness. Adding the later-origin vectors and using
(NH25) gives \(3+3(m-2)=3m-3\) independent proper weak functions,
on which the residue map is injective by (NH27). Together with the
\(3m\) binary residue pivots, this constructs a graded subsystem of
rank at least \(6m-3\).

Thus this construction leaves three directions: a possible
constant-function/infinity ambiguity and the two polynomial head
gauges. The constant direction has not been excluded from the actual
image in (NH26), and those polynomial gauges have not been coupled
to the remaining weak observations. In particular, it would be
incorrect to infer that only two directions remain from full weak
function independence. The exact paired determinant and the
retained-old-source step are still unproved.

## Two actual gauges and the explicit three-dimensional test

The remaining scalar complement can be stated explicitly. Let
\(p_0=e_0\) and \(p_1=-re_1\). Suppose actual completed coefficient
vectors \(\gamma_0,\gamma_1\) have binary rows \(p_0,p_1\).
Their exact row sums are respectively \(1,-r\). Such gauges exist
by the binary scalar lifting theorem and the checked base. Their
source polynomial heads are retained throughout this construction.

For an append, set \(g_b=(p_bK_k^0)_1\) and
\(q_b=g_b-(p_b)_1\). The actual update is
\(\gamma_b^+=\iota(\gamma_b)-\mathcal C_{q_b}\), where
\(\mathcal C_{q_b}\) is an exact-sum-zero binary lift at length \(k\).
Its binary row is again \(p_b\), and its head is the old head minus
the lift's actual head. No ambient polynomial preimage is assumed.
The two targets are

\[
 q_0=\frac{-Ar}{2-Ar},\quad
 \frac{q_0}{d_k}=\frac{1-2Ar}{3},\qquad
 q_1=\frac r{1-2Ar},\quad
 \frac{q_1}{d_k}=-\frac2{3A}+\frac r3.
 \tag{NH28}
\]

Use the actual head differences (NH18) with coefficients
\[
 \begin{array}{c|cc}
 &\mathcal H_{k,0}&\mathcal H_{k,1}\\ \hline
 q_0&-A/(A-a_m)&-2Aa_m/(A-a_m)\\
 q_1&2/(A-a_m)&a_m/(A-a_m).
 \end{array}
 \tag{NH29}
\]
In each row, subtracting these two binary outputs from \(q_b\) and
dividing by \(d_k\) leaves a bounded old scalar that is zero at zero,
by (NH19) and (NH28). Append its actual shorter lift. This constructs
the required \(\mathcal C_{q_b}\).

The last-kernel identity then gives the two updated gauge weak functions
\[
 \begin{split}
 c_{\gamma_0^+}
   &=\frac{b_k}{3}+\frac A{A-a_m}W_0
                      +\frac{2Aa_m}{A-a_m}W_1,\\
 c_{\gamma_1^+}
   &=\frac{b_k}{3A}-\frac2{A-a_m}W_0
                      -\frac{a_m}{A-a_m}W_1.
 \end{split}
 \tag{NH30}
\]
Indeed the inherited gauge contributes
\(b_ks_b/3-b_k\mathcal A_k g_b\), whereas its zero-sum section
contributes \(-b_k\mathcal A_kq_b\) plus the two defects in (NH29).
For \(b=1\), the remaining polynomial expression is
\(-b_kr/3+b_k\mathcal A_kr=b_k/(3A)\).
This calculation does not transport the old gauge's weak scalar:
that older scalar first enters the appended output at the next
\(\delta\) order.

The coefficient determinant of \(W_0,W_1\) in (NH30) is
\(3Aa_m/(A-a_m)^2\ne0\). Consequently
\[
 \operatorname{span}\{1,c_{\gamma_0^+},c_{\gamma_1^+}\}
       =\operatorname{span}\{1,W_0,W_1\}=:\mathcal V_k.
 \tag{NH31}
\]
Another exact simplification is
\(W_1=-rW_0-r\Delta_kD_k\): the binary row difference of the
moved-first product is its determinant \(D_k\).

The gauges remain independent modulo the exact-sum-zero coefficient
space because their completed sums are \(1,-r\). Together with the
actual binary section and promoted kernel vectors, they form an actual
coefficient basis; the positive-order promotion corrections preserve
its unit determinant.

Write \(\mathcal S_k\) for the full actual promoted weak-function
image in (NH26), of dimension \(3k-2\). Since the ambient
\(\mathcal F_k\) has dimension \(3k+1\), the remaining condition is
precisely
\[
 \boxed{\mathcal S_k\cap\mathcal V_k=\{0\},
        \qquad \mathcal V_k=\operatorname{span}\{1,W_0,W_1\}.}
 \tag{NH32}
\]
If this transversality holds, (NH31) and (NH27) show that the
\(3k-2\) promoted kernel columns and the two gauge columns have
independent weak residues. Combined with the \(3k\) strong binary
pivots, the leading normalized graded determinant is then nonzero.
Conversely that leading weak-residue independence gives (NH32).

Thus (NH32) is an explicit three-dimensional test, with both actual
gauge functions known. Its vanishing or nonvanishing has not been
established uniformly in \(k\). The direct-sum transfer alone does
not prove this transversality, and does not yet close paired induction.

## Separating the gauge space from the new weak image

The following reductions are independently audited paper arguments. They
concern the particular recursively promoted actual space \(\mathcal S_m\)
in (NH26), not the space of every possible higher-order weak coefficient.
Continue to write \(k=m+1\), with \(m\ge2\), and put

\[
 z=2h,\qquad
 \ell=\frac{b_k-b_m}{3},\qquad
 \omega=\frac{b_k/A-b_m/a_m}{3},\qquad
 \Delta_k=\ell+\frac\omega r,\qquad
 \zeta=-\frac\omega\ell.
 \tag{NH33}
\]

In addition to the earlier units, suppose \(\ell\ne0\),
\(A b_m-a_m b_k\ne0\), and \(\zeta\) avoids the old and new
poles. These are generic conditions compatible with positive parameters.
Every member of \(\mathcal N_k\) vanishes at \(0,\infty,\zeta\).
Write \(w_{00}=W_0(0)\), \(w_{1\infty}=W_1(\infty)\), as in
(NH22). Evaluation of \((1,W_0,W_1)\) at these three points gives

\[
 \begin{pmatrix}
 1&w_{00}&0\\
 1&0&w_{1\infty}\\
 1&-\ell&\ell\zeta
 \end{pmatrix},\qquad
 \det=
 \frac{(A b_m-a_m b_k)(b_k-b_m)}{12Aa_m}\ne0.
 \tag{NH34}
\]

Indeed the determinant before simplification is
\(w_{00}w_{1\infty}+\ell w_{1\infty}
-\ell\zeta w_{00}\). Substitution of (NH22) proves the displayed
factorization. Therefore
\(\dim\mathcal V_k=3\) and \(\mathcal V_k\cap\mathcal N_k=0\).
This is a sufficient generic evaluation test. At either excluded weight
value where its determinant vanishes, it does **not** establish an
intersection of the two function spaces.

## An explicit old preimage of the three-dimensional test

Let \(Q=Q_{1,h}\), and use \(\overline\beta\) from (NH12). Define

\[
 \begin{split}
 \Omega(r)&=
 \frac{\Delta_k(r)D_m(r)\overline\beta(r)}
      {\Delta_k(z)D_m(z)\overline\beta(z)},\\
 G_1&=W_0+\frac{\Delta_kD_m\beta_0}{Q(2/A)},\qquad
 G_2=W_1+\frac{\Delta_kD_m\beta_1}{Q(1/(2A))}.
 \end{split}
 \tag{NH35}
\]

The two added terms cancel, respectively, the only new state-0 pole of
\(W_0\) and the only new state-1 pole of \(W_1\). Thus \(G_1,G_2\)
have only old poles. The same is true of \(\Omega\), which belongs
to \(\mathcal N_k\), has value one at \(z\), and has values zero
at zero and infinity. All denominators in (NH35) are units by
(NH11)--(NH13).

For a target \(F=\nu+\rho W_0+\sigma W_1\), set

\[
 \begin{aligned}
 c_0&=F(0)/\kappa_0,&c_\infty&=F(\infty)/\kappa_\infty,\\
 \Lambda_0&=2hA/(A-a_m),&\Lambda_\infty&=-a_m/(A-a_m),\\
 u_1&=\rho+\Lambda_0c_0,&u_2&=\sigma+\Lambda_\infty c_\infty,\\
 G&=\nu+u_1G_1+u_2G_2,&
 c_*&=\frac{G-G(z)\Omega}{\chi_{k,h}}.
 \end{aligned}
 \tag{NH36}
\]

This is the unique old preimage in the direct-sum decomposition (NH25):

\[
 c_*\in\mathcal F_m,\qquad c_*(\xi)=0,\qquad
 \mathscr T^{\rm full}_{k,h}(c_*)\equiv F\pmod{\mathcal N_k}.
 \tag{NH37}
\]

For the verification, \(G-G(z)\Omega\) has only simple old poles
and vanishes at \(z\), so division by the simple zero of \(\chi\)
is removable. The reciprocal of \(\chi\) vanishes at \(\xi\),
and the numerator is regular there, giving \(c_*(\xi)=0\).
The resulting function is bounded at infinity. At the two endpoints,
\(\kappa_0=\chi(0)-\Lambda_0w_{00}\) and
\(\kappa_\infty=\chi(\infty)-\Lambda_\infty w_{1\infty}\)
show that its values are exactly \(c_0,c_\infty\). Substituting in
(NH23) leaves \(F\) modulo the three terms in \(\mathcal N_k\)
used in (NH35)--(NH36). Uniqueness follows from (NH25).

Let \(\mathcal U_k\subset\mathcal F_m\) be the preimage of
\(\mathcal V_k\) modulo \(\mathcal N_k\). By (NH34) it has
dimension three. The exact actual-space condition is now

\[
 \mathcal S_k\cap\mathcal V_k=0
 \quad\Longleftrightarrow\quad
 \mathcal S_m\cap\mathcal U_k=0.
 \tag{NH38}
\]

In particular, every member of \(\mathcal U_k\) vanishes at the
new point \(\xi\). It is not literally the previous gauge space,
which contains the constant function one. No replacement of the old
actual space by an arbitrary ambient complement is made here.

## An affine pencil in the new weak weight

There is a useful frame for the same preimage with polynomial dependence
on \(b_k\). Put

\[
 p=(K_1^0\cdots K_m^0)_{01},\qquad
 q_0=\frac{-Ar}{2-Ar},\qquad q_1=\frac{-2Ar}{1-2Ar}.
\]

Binary affine composition, with the indicated word order, gives
\(B_{{\rm new},0}=p+D_mq_0\) and
\(B_{{\rm new},1}=-r(p+D_mq_1)\). Define

\[
 \begin{array}{c|c|c}
 i&F_i&L_i\\ \hline
 0&p+D_m(q_0+\beta_0/Q(2/A))&1\\
 1&-rp+D_m(-rq_1+\beta_1/Q(1/(2A)))&-r\\
 2&D_m\overline\beta&0
 \end{array}
 \qquad
 g_i=\Delta_kF_i+\frac{b_m-b_k}{3}L_i.
 \tag{NH39}
\]

Thus \(g_0=G_1\), \(g_1=G_2\), and
\(g_2=\Delta_kD_m\overline\beta\). The subspace of
\(\mathcal V_k+\mathcal N_k\) with its new state-0 and state-1
poles removed has basis \(1,g_0,g_1,g_2\): the two new-pole
conditions are independent, and (NH34) excludes a remaining intersection.
Imposing value zero at \(z\) gives the frame
\(g_i-g_i(z)\). Division by \(\chi\), omitting the common nonzero
factor \(3/(4b_k)\), therefore gives a basis of \(\mathcal U_k\):

\[
 \begin{split}
 c_i&=\frac{1-Ar}{r-z}\bigl(g_i(r)-g_i(z)\bigr)
          =b_k u_i-b_m v_i,\\
 u_i&=\mathcal D_{A,z}\bigl(\mathcal A_kF_i-L_i/3\bigr),\\
 v_i&=\mathcal D_{A,z}\bigl(\mathcal A_mF_i-L_i/3\bigr),\\
 \mathcal D_{A,z}f&=\frac{1-Ar}{r-z}\bigl(f(r)-f(z)\bigr).
 \end{split}
 \tag{NH40}
\]

Here \(u_i,v_i\) depend on the old parameters, \(A,h\), but not
on \(b_k\). Choose any coordinates on the three-dimensional old
quotient \(\mathcal F_m/\mathcal S_m\). In these coordinates the
remaining test is the determinant of the three columns in (NH40), an
affine matrix pencil in \(b_k\), whose determinant has degree at most
three. No exact degree, particular factor, sign, or nonzero coefficient
has been proved. In particular, the two factors in the sufficient
evaluation test (NH34) are not thereby factors of this actual quotient
determinant. The unresolved obligation is to prove that at least one
coefficient of this polynomial is nonzero for the actual old quotient,
uniformly in the length.

## Restriction to binary poles and the first state-2 pole

The preimage test can be restricted further without an old source
inverse. Let \(\mathcal F_m^{(1)}\) be the bounded rational functions
whose only possible poles are the \(2m\) old state-0 and state-1
nodes, together with \(1/a_1\). Define the actual subspace

\[
 \dim\mathcal F_m^{(1)}=2m+2,\qquad
 \mathcal S_m^{(1)}=\mathcal S_m\cap\mathcal F_m^{(1)}.
 \tag{NH41}
\]

Every function in \(\mathcal U_k\) lies in \(\mathcal F_m^{(1)}\).
To see this directly from (NH39), the word defining \(p\) starts in
state zero and every binary kernel has zero output-2 column. It therefore
uses only binary row denominators. The factors \(D_m\) also have only
binary poles, while \(Q_{1,h}\), and consequently
\(\overline\beta\), can add only the first state-2 pole. The
cancellations and divided differences above introduce no other old
poles. The same observation proves
\(\mathcal N_k\subset\mathcal F_k^{(1)}\).

For any old state-2 node \(1/a_t\), \(t\ge2\), the only term of
(NH23) with a pole there is \(\chi_{k,h}c\). Its residue is the
old residue multiplied by the nonzero value \(\chi_{k,h}(1/a_t)\).
At the new state-2 node, the earlier pole calculation shows that the
residue vanishes exactly when \(c(\xi)=0\). Thus the actual recursive
decomposition \(\mathcal S_k=\mathcal N_k\oplus
\mathscr T^{\rm full}_{k,h}\mathcal S_m\) restricts exactly to

\[
 \boxed{\mathcal S_{m+1}^{(1)}
  =\mathcal N_{m+1}\oplus
    \mathscr T^{\rm full}_{m+1,h}
       \bigl(\mathcal S_m^{(1)}\cap\ker\operatorname{ev}_{1/a_{m+1}}\bigr).}
 \tag{NH42}
\]

On this restricted domain \(\lambda=0\), so the transfer simplifies
to \(\chi c-\Lambda_0c(0)W_0-\Lambda_\infty c(\infty)W_1\).
This simplification retains both actual endpoint corrections.

For completeness, the base has \(\dim\mathcal S_2^{(1)}=3\)
generically. The four-dimensional base image loses one dimension on
removing its second state-2 pole. A concrete nonzero witness follows
from (TB11), (TB16)--(TB18) in
[SOURCE24_BINARY_TWO_BLOCK_BASE.md](SOURCE24_BINARY_TWO_BLOCK_BASE.md).
At \(h=0\), \(b_1=b_2=\beta\), \(a_1=1,a_2=3\), its actual
completed-kernel vector is

\[
 \kappa_{22}=j_{22}-\frac56h_{21}-\frac13h_{22}
                    +\frac12h_{11}-\frac14j_{20}-\frac1{12}j_{10}.
 \tag{NH43}
\]

In the weak scalar \(c=[\delta]C_2/r\), only \(j_{22},h_{22},j_{10}\)
can have a pole at \(r=1/3\). Their coefficients of \(1/(1-3r)\)
are respectively \(0,-4\beta/5,4\beta/5\). Formula (NH43)
therefore has coefficient \(\beta/5\), or ordinary residue
\(-\beta/15\). All six nodes are distinct. This rational witness
need not lie in \(a_t\in(1,2)\): it proves the residue's cleared
polynomial is nonzero, hence it is nonzero generically on that positive
open set as well. Binary rank is constant near the checked base, so its
exact-sum-zero binary kernel admits a regular local continuation in
\(h\); the residue nonvanishing continues to generic nonzero \(h\).

At each subsequent step, evaluation at the independent new point
\(1/a_{m+1}\) has rank one on the nonzero old rational-function
space \(\mathcal S_m^{(1)}\). A nonzero rational function cannot
vanish identically as that point varies in an interval. Consequently
(NH42) adds exactly two dimensions and proves

\[
 \boxed{\dim\mathcal S_m^{(1)}=2m-1,\qquad
 \mathcal S_k\cap\mathcal V_k=0
 \Longleftrightarrow
 \mathcal S_m^{(1)}\cap\mathcal U_k=0.}
 \tag{NH44}
\]

The smaller ambient quotient
\(\mathcal F_m^{(1)}/\mathcal S_m^{(1)}\) still has dimension
three. Its natural map to \(\mathcal F_m/\mathcal S_m\) is
injective and therefore an isomorphism. It may replace that quotient
in the affine pencil (NH40). Equations (NH42)--(NH44) give an exact
evaluation recurrence for the actual accumulated space, but do not
establish the remaining determinant's nonvanishing. No conclusion
about full paired independence or Eq. (24) follows without that step.

## A fixed old span for the entire new-parameter preimage family

The functions in (NH39) admit exact cancellations that remove all
dependence of their pole set on the new parameter. Put \(a=a_1\),
\(Q_0=Q(2/A)\), \(Q_1=Q(1/(2A))\), \(Q_\xi=Q(1/A)\), and
write \(F_0=p+D_mR_0\), \(F_1=-rp+D_mR_1\), \(F_2=D_mR_2\).
Then
\[
 \begin{aligned}
 R_0&=\frac{u_0r+v_0}{1-ar},
 &u_0&=-a\left(1+\frac2{3AQ_0}\right),
 &v_0&=-\frac{2h}{3Q_0},\\
 R_1&=\frac{r(u_1r+v_1)}{1-ar},
 &u_1&=a\left(1+\frac1{6AQ_1}\right),
 &v_1&=\frac{2h}{3Q_1},\\
 R_\xi&=\frac{u_\xi r+v_\xi}{1-ar},
 &u_\xi&=-a\left(1+\frac1{3AQ_\xi}\right),
 &v_\xi&=-\frac{2h}{3Q_\xi},\\
 R_2&=R_1+2hR_0+(r-2h)R_\xi.
 \end{aligned}
 \tag{NH45}
\]
Indeed the defining numerators of \(R_0,R_1,R_\xi\) vanish at
\(2/A,1/(2A),1/A\), respectively. Polynomial division gives
the displayed coefficients. For the last identity use
\[
 d_kQ_{k,h}=2h q_0-rq_1+(r-2h)\frac{-Ar}{1-Ar},
 \qquad
 R_\xi=\frac{-Ar+Q/Q_\xi}{1-Ar}.
\]
Substituting the definition of \(\overline\beta\) proves (NH45).
In particular its numerator has degree at most two, with coefficients
\[
 \begin{split}
 [r^2](1-ar)R_2&=\frac a{6A}\left(\frac1{Q_1}-\frac2{Q_\xi}\right),\\
 [r](1-ar)R_2&=\frac{2h}3
  \left[\frac1{Q_1}-\frac1{Q_\xi}
       +\frac aA\left(\frac1{Q_\xi}-\frac2{Q_0}\right)\right],\\
 [1](1-ar)R_2&=\frac{4h^2}3
                       \left(\frac1{Q_\xi}-\frac1{Q_0}\right).
 \end{split}
 \tag{NH46}
\]

Let \(P=D_m/(1-ar)\) and
\(Jf=(f(r)-f(z))/(r-z)\), with \(z=2h\ne0\).
Modulo constants, the three \(g_i\) belong to
\(\operatorname{span}\{p-1,p/r,r(p-1),P/r,P,Pr,Pr^2\}\).
For example the polynomial term in \(g_1\) combines with its
\(-r\Delta_kp\) term to give a multiple of \(r(p-1)\).
The identities
\[
 J(rf)=f+zJf,\qquad
 J(f/r)=\frac{Jf-f/r}{z},\qquad
 (1-Ar)Jf=(1-Az)Jf-A(f-f(z))
\]
now give, for every admissible choice of new \(A,b_k\),
\[
 \boxed{\mathcal U_k\subseteq
  \mathcal B_m:=
  \operatorname{span}\{1,p,p/r,r(p-1),Jp,P/r,P,Pr,Pr^2,JP\},
  \qquad \dim\mathcal B_m\le10.}
 \tag{NH47}
\]
This is a space fixed by the old parameters and \(h\). At zero,
\(p=O(r)\) and \(P=O(r^m)\); at infinity,
\(p=1+O(1/r)\) and \(P=O(r^{-m-1})\).
These facts establish boundedness and regularity of every displayed
generator for \(m\ge2\). The divided difference removes the apparent
pole at \(z\), and introduces no higher-order old poles. Thus
\(\mathcal B_m\subseteq\mathcal F_m^{(1)}\).

The exact cancellations and spanning assertion were independently
audited. This gives a bounded-dimensional representation of the whole
preimage family, not a closed transfer recurrence for
\(\mathcal S_m^{(1)}\cap\mathcal B_m\). That intersection and the
nonzero-coefficient obligation in (NH40) remain unresolved.

## The inverse transfer on a general scalar

The quotient inverse can be constructed by local evaluations for every
\(F\in\mathcal F_k\), not only for the three targets in (NH36).
The following inverse and dual formulas have been independently audited.
Retain \(k=m+1\ge3\), \(z=2h\), and all the preceding generic
units. Write \(\chi=\chi_{k,h}\), and distinguish the scaled line
residues from ordinary \(r\)-residues by

\[
 \begin{aligned}
 (p_0,p_1,p_2)&=(2/A,1/(2A),\xi),&
 \mathcal R_jF&=(l_{kj}F)(p_j)
                   =l'_{kj}\operatorname{Res}_{r=p_j}F,\\
 (l'_{k0},l'_{k1},l'_{k2})&=(-A,-2A,-A),&
 \mathsf N_j&=\Delta_kD_m\beta_j\quad(j=0,1),\\
 n_j&=\mathcal R_j\mathsf N_j,&
 \mathsf Z&=\Delta_kD_md_kQ_{k,h}.
 \end{aligned}
 \tag{NH48}
\]

The two \(n_j\) are nonzero, and
\(\mathcal R_0\mathsf N_1=\mathcal R_1\mathsf N_0=0\).
Set

\[
 \begin{aligned}
 \eta&=\frac1{D_m(\xi)(\xi-z)(4b_k/3+\Delta_k(\xi))},&
 \lambda&=\eta\mathcal R_2F,\\
 \alpha_0&=\frac{\Lambda_0}{\kappa_0}F(0),&
 \alpha_\infty&=\frac{\Lambda_\infty}{\kappa_\infty}F(\infty),\\
 Y&=F+\lambda\mathsf Z+\alpha_0W_0+\alpha_\infty W_1,&
 Y_c&=Y-\frac{\mathcal R_0Y}{n_0}\mathsf N_0
          -\frac{\mathcal R_1Y}{n_1}\mathsf N_1,\\
 \mathcal P_kF&=\frac{Y_c-Y_c(z)\Omega}{\chi}.&&
 \end{aligned}
 \tag{NH49}
\]

Here \(\Omega\) is the normalized old-pole-only function in (NH35).
The subtractions defining \(Y_c\) remove the new active poles.
The final subtraction removes the apparent pole at the zero \(z\)
of \(\chi\). At the new state-2 pole, put
\(c_\xi=\lambda D_m(\xi)\). The identity
\(\mathcal R_2(d_kQ_{k,h})=z-\xi\) gives
\(\mathcal R_2Y_c=(\xi-z)(4b_k/3)c_\xi\), so division by
\(\chi\) is regular there and has value \(c_\xi\).
The endpoint identities in (NH24) give values
\(F(0)/\kappa_0,F(\infty)/\kappa_\infty\) for the resulting
old scalar. It has only simple old poles and is bounded at infinity.
Substitution into (NH23) therefore proves

\[
 \boxed{\begin{aligned}
 \mathcal P_kF&\in\mathcal F_m,&
 \mathscr T^{\rm full}_{k,h}\mathcal P_kF&\equiv F\pmod{\mathcal N_k},\\
 \mathcal P_k\mathscr T^{\rm full}_{k,h}&=I,&
 \ker\mathcal P_k&=\mathcal N_k.
 \end{aligned}}
 \tag{NH50}
\]

In particular \(\mathcal P_k\) is surjective. This is the inverse
of the proved scalar direct sum (NH25), constructed without an old
paired-matrix or source inverse.

## Three actual quotient functionals and their recurrence

Choose a rank-three linear map \(L_2:\mathcal F_2\to\mathbb K^3\)
whose kernel is the checked four-dimensional actual base image
\(\mathcal S_2\), over the generic rational parameter field
\(\mathbb K\). It can be specified in the seven coordinates given
by the six ordinary residues and the value at infinity. Define

\[
 \boxed{L_k=L_m\mathcal P_k,\qquad
 L_m=L_2\mathcal P_3\cdots\mathcal P_m,\qquad
 \operatorname{rank}L_m=3,\quad\ker L_m=\mathcal S_m.}
 \tag{NH51}
\]

The rightmost map acts first in the composition. Surjectivity in
(NH50) preserves rank, and its kernel identity together with
\(\mathcal S_k=\mathcal N_k\oplus
\mathscr T^{\rm full}_{k,h}\mathcal S_m\) proves the kernel claim.
Thus these are functionals on the actual recursively promoted space;
no arbitrary ambient complement is substituted for that space.

One can propagate them using divided differences at \(z\). Write
\(F_{[j]}=F^{(j)}(z)/j!\) for normalized Taylor coefficients.
Formula (NH49), with \(\Omega_{[0]}=1\), gives

\[
 (\mathcal P_kF)_{[j]}=\frac3{4b_k}
 \left[(1-Az)(Y_{c,[j+1]}-Y_{c,[0]}\Omega_{[j+1]})
       -A(Y_{c,[j]}-Y_{c,[0]}\Omega_{[j]})\right].
 \tag{NH52}
\]

A pullback raises the needed Taylor order by at most one. Starting
with residue/infinity functionals at length two, the three rows of
\(L_m\) can therefore be expressed using current pole residues,
endpoint values, and derivatives at \(z\) through order at most
\(m-3\) for \(m\ge3\). The potential highest-jet multiplier is
\(3(1-Az)/(4b_k)\ne0\). This is an upper bound on the required
order, not a claim that all those coefficients are nonzero, and not
a fixed-order differential closure of the span in (NH47).

Alternatively, the dual recurrence stays entirely in residue coordinates.
For one old functional write
\(\ell(c)=a_\infty c(\infty)+\sum_\rho w_\rho
\operatorname{Res}_\rho c\), where \(\rho\) runs over old nodes.
For \(U\in\{W_0,W_1,\mathsf Z,\mathsf N_0,\mathsf N_1\}\), set

\[
 \theta=\sum_\rho\frac{w_\rho}{\chi(\rho)}
                       \operatorname{Res}_\rho\Omega,\qquad
 \Gamma_U=\sum_\rho\frac{w_\rho}{\chi(\rho)}
           \operatorname{Res}_\rho\bigl(U-U(z)\Omega\bigr).
 \tag{NH53}
\]

Define the five coefficients

\[
 \begin{aligned}
 A_0&=\frac{\Lambda_0}{\kappa_0}
       \left(\Gamma_{W_0}-\frac{\mathcal R_0W_0}{n_0}
                                        \Gamma_{\mathsf N_0}\right),\\
 A_\infty&=\frac{\Lambda_\infty}{\kappa_\infty}
       \left(\Gamma_{W_1}-\frac{\mathcal R_1W_1}{n_1}
                                        \Gamma_{\mathsf N_1}\right),\\
 B_0&=-\Gamma_{\mathsf N_0}/n_0,\qquad
 B_1=-\Gamma_{\mathsf N_1}/n_1,\\
 B_2&=\eta\left(\Gamma_{\mathsf Z}
       -\frac{\mathcal R_0\mathsf Z}{n_0}\Gamma_{\mathsf N_0}
       -\frac{\mathcal R_1\mathsf Z}{n_1}\Gamma_{\mathsf N_1}\right).
 \end{aligned}
 \tag{NH54}
\]

Expanding (NH49), using
\(\mathcal R_0W_1=\mathcal R_1W_0=0\), gives the exact update

\[
 \boxed{\ell(\mathcal P_kF)=
  \frac{a_\infty}{\kappa_\infty}F(\infty)
  +\sum_\rho\frac{w_\rho}{\chi(\rho)}\operatorname{Res}_\rho F
  -\theta F(z)+A_0F(0)+A_\infty F(\infty)
  +\sum_{j=0}^2B_j\mathcal R_jF.}
 \tag{NH55}
\]

For bounded simple-pole functions,
\(F(z)=F(\infty)+\sum_x\operatorname{Res}_xF/(z-x)\) and
\(F(0)=F(\infty)-\sum_x\operatorname{Res}_xF/x\), with the sums
over all current nodes. Thus (NH55) is again a residue/infinity
functional: its old-node weight is
\(w_\rho/\chi(\rho)-\theta/(z-\rho)-A_0/\rho\), its new-node
weight is \(-\theta/(z-p_j)-A_0/p_j+B_jl'_{kj}\), and its
infinity coefficient is
\(a_\infty/\kappa_\infty-\theta+A_0+A_\infty\).
The line-residue slopes in (NH48) are essential in this conversion.

This provides an explicit recurrence for all three quotient rows using
known binary functions and local residues. The remaining test is still
\(\det[L_k(1),L_k(W_0),L_k(W_1)]\ne0\), or equivalently the
preimage pencil (NH40) evaluated by \(L_m\). Neither the inverse
formula nor propagation of the three annihilators proves that determinant
nonzero. Full paired independence and Eq. (24) remain open.

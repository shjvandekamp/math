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

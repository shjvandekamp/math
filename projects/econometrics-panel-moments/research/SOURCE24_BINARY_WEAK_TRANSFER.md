# Three explicit terminal pivots for the first weak-output transfer

Status: independently audited paper derivation.
This is not formalized in Lean. The theorem below concerns three actual
completed-column combinations at the binary boundary \(h=0\). It does not
establish separation through every older graded layer or prove paired/source
independence. The later sections prove an explicit two-layer separation and
an obstruction to continuing that separation at the binary boundary.

The notation and explicit binary lifting section come from
[SOURCE24_SCALAR_LAURENT_SPANNING.md](SOURCE24_SCALAR_LAURENT_SPANNING.md),
especially (SL28)–(SL35). The common-tail setting is (LC191)–(LC195) of
[SOURCE24_LAST_TIME_COALESCENCE.md](SOURCE24_LAST_TIME_COALESCENCE.md).

## Setup and actual inherited columns

Fix \(k=m+1\ge3\),

\[
 G=\begin{pmatrix}2&1&1\\1&2&1\\1&1&2\end{pmatrix},\quad
 X=(1,-r,r),\quad v=(0,-r,r),\quad
 A_t=G\operatorname{diag}(1,a_t,b_t\delta),\quad
 K_t=\operatorname{diag}(A_tX)^{-1}A_t\operatorname{diag}X.
 \tag{BW1}
\]

Assume the \(a_t\in(1,2)\) are distinct and every \(b_t\ne0\). All basic
column combinations have coefficients constant in the effect coordinate
\(r\) and in \(\delta\). They may depend on the table parameters. The later
order-raising construction explicitly permits formal-power-series coefficients
in \(\delta\), still constant in \(r\).

The actual completed columns at length \(k\) are

\[
 C^H_{sb}=X_be_bP_s,\qquad C^J_{tc}=\mu_{tc}vP^t,
 \quad
 P_s=K_sK_1\cdots\widehat K_s\cdots K_k,\quad
 P^t=K_1\cdots\widehat K_t\cdots K_k,
 \quad
 (\mu_{t0},\mu_{t1},\mu_{t2})
       =\left(\frac2{L_{t0}},\frac{-r}{L_{t1}},\frac r{L_{t2}}\right).
 \tag{BW2}
\]

Here \(L_{tc}=(A_tX)_c\). The corresponding source rows are
\(H_{sb}=X_be_b-C^H_{sb}\), \(J_{tc}=-C^J_{tc}\).
For \(s,t\le m\), the length-\(k\) completed column is exactly its
length-\(m\) version multiplied on the right by \(K_k\). This retains
the actual moved-first and omitted-factor orders.

At \(\delta=0\), set

\[
 l_{t0}=2-a_tr,\quad l_{t1}=1-2a_tr,\quad l_{t2}=1-a_tr,
 \quad d_t=\frac{-3a_tr}{l_{t0}l_{t1}},\quad
 D_o=\prod_{t\le m}d_t,
 \quad Q=Q_1=-\frac{r(2-a_1r)}{3(1-a_1r)},
 \quad \mathcal A_t=\frac{1+a_tr}{3a_tr}.
 \tag{BW3}
\]

Use \(\mathcal A_t\) for this scalar to distinguish it from the table
\(A_t\). The shorter binary scalar space \(\mathcal B_m\) consists of
rational functions with simple poles only at the \(3m\) old nodes,
bounded at infinity and zero at \(r=0\). By (SL34), every
\(f\in\mathcal B_m\) has an actual completed lift \(\mathcal C_f\)
whose row sum is identically zero and whose binary limit is

\[
 \mathcal C_f\big|_{\delta=0}=(-f,f,0).
 \tag{BW4}
\]

The Laurent basis in (SL30)–(SL33) provides an explicit section: remove
the state-2 residues, then peel the two Laurent extremes successively.
This uses no paired-source inverse. The chosen effect-constant coefficients
are held fixed as \(\delta\) varies, so the lift has exact zero row sum
before taking its limit.

## Three terminal combinations and their shorter lifts

Write \(A=a_k\), \(a=a_1\), \(\xi=1/A\). Let

\[
 Z_k=C^H_{k1}+C^H_{k2},\qquad
 E_0=C^J_{k0},\qquad E_1=C^J_{k1},\qquad
 E_2=Z_k+Q(\xi)^{-1}C^J_{k2}.
 \tag{BW5}
\]

Every \(E_j\) has row sum zero for all \(\delta\). The denominator
\(Q(\xi)\) is nonzero since \(a\ne A\) and \(a,A\in(1,2)\).
Define \(B_j=(E_j|_{\delta=0})_1\), and write \(B_j=D_o\beta_j\).
Direct ordered-word multiplication gives

\[
 \begin{split}
 \beta_0&=\frac{2Q}{2-Ar},\\
 \beta_1&=\frac{-rQ}{1-2Ar},\\
 \beta_2&=\frac{Ar^2}{(1-2Ar)(1-Ar)}
              +\frac{rQ}{Q(1/A)(1-Ar)}.
 \end{split}
 \tag{BW6}
\]

For the incoming terms, \((vK_1\cdots K_m)_1=D_oQ\). For the head
sum, \((Z_k|_0)_1=D_od_kQ_k\), where
\(Q_k=-r(2-Ar)/(3(1-Ar))\); hence \(d_kQ_k=Ar^2/((1-2Ar)(1-Ar))\).
This proves (BW6) with the displayed signs.

The possible new state-2 pole in \(\beta_2\) cancels exactly: at
\(r=\xi\), its two numerator contributions are \(-1/A\) and \(1/A\).
Define

\[
 f_j=-B_j/d_k.
 \tag{BW7}
\]

These functions belong to \(\mathcal B_m\). Indeed, multiplication by
\(d_k^{-1}\) cancels the new state-0 and state-1 poles, and (BW6) has
already canceled the state-2 pole. It introduces only a possible pole
at zero. But \(B_0=O(r^{m+1})\), \(B_1,B_2=O(r^{m+2})\) there, while
\(d_k\) has a simple zero. Thus \(f_j(0)=0\). At infinity,
\(D_o=O(r^{-m})\), \(\beta_0=O(1)\), and
\(\beta_1,\beta_2=O(r)\); dividing by \(d_k=O(r^{-1})\) leaves
\(f_j=O(r^{2-m})\), which is bounded because \(m\ge2\).

Choose the lifts (BW4) for these \(f_j\), and form the actual combinations

\[
 Y_j=E_j+\mathcal C_{f_j}K_k.
 \tag{BW8}
\]

Their row sums vanish exactly. The appended shorter binary output is
\(d_k f_j=-B_j\), so

\[
 Y_j\big|_{\delta=0}=0.
 \tag{BW9}
\]

Thus these are actual leading-kernel combinations, not arbitrary
ambient interpolants. For the corresponding source combinations, the
leading row can still contain its polynomial head; that head has no
old-node residues.

## Exact first weak-output map

For a completed word ending in \(K_l\), with a nonempty prefix, the
terminal identity (SL10) implies

\[
 \left.\frac{C_2}{\delta X_2}\right|_0
      =\frac{b_l}{3}(C\mathbf1)
                     -b_l\mathcal A_l(C|_0)_1.
 \tag{BW10}
\]

The prefix output 2 is \(O(\delta)\), so the third term of (SL10) is
\(O(\delta^2)\). In (BW8), every inherited word ends in \(K_k\), while
every term of \(E_j\) ends in \(K_m\). The latter includes the omitted
word of \(C^J_{kc}\), whose length is \(m\ge2\). Thus (BW10) applies
to all terms, including the case \(m=2\).

Using their exact zero row sums and opposite leading output-1 values gives

\[
 \boxed{
 \left.\frac{(Y_j)_2}{\delta X_2}\right|_0
     =\bigl(b_k\mathcal A_k-b_m\mathcal A_m\bigr)B_j.}
 \tag{BW11}
\]

The formula is independent of the choice of shorter binary lift. A
different lift changes the inherited completed row by a zero-row-sum
combination with zero binary limit; (BW10) gives zero first weak-output
coefficient for its appended copy.

## A nonzero three-dimensional terminal map

The three \(B_j\) are independent. First, \(\beta_0\) has an exclusive
new state-0 pole at \(r=2/A\), with nonzero residue. The other two have
the canceled forms

\[
 \begin{split}
 \beta_1&=\frac{r^2(2-ar)}{3(1-2Ar)(1-ar)},\\
 \beta_2&=\frac{Ar^2\bigl((4A-3a)-2a(A-a)r\bigr)}
                  {(2A-a)(1-2Ar)(1-ar)}.
 \end{split}
 \tag{BW12}
\]

After removing their nonzero common rational factors, the two linear
numerators have coefficient determinant

\[
 \det\begin{pmatrix}2&-a\\4A-3a&-2a(A-a)\end{pmatrix}=a^2\ne0.
 \tag{BW13}
\]

Multiplication by \(D_o\) preserves independence. So does the common
factor in (BW11):

\[
 b_k\mathcal A_k-b_m\mathcal A_m
   =\frac13\left(b_k-b_m+
                   \frac{b_k/a_k-b_m/a_m}{r}\right)\not\equiv0.
 \tag{BW14}
\]

If both coefficients vanished, nonzero \(b_m,b_k\) would force
\(a_k=a_m\), contrary to the assumptions. Therefore the three first
weak-output scalar coefficients in (BW11) are independent.

This proves a uniform rank-three terminal map for every \(k\ge3\),
using explicit actual terminal columns and the proved shorter binary
section. The restriction \(m\ge2\) is needed both for boundedness in
(BW7) and for the incoming terminal cancellation in (BW10).

The theorem is stated at \(h=0\). Continuation away from this boundary
must preserve the exact row-sum condition, replacing \(Z_k\) by
\(2hC^H_{k0}+C^H_{k1}+C^H_{k2}\), and continue both the pole-canceling
constant and the shorter section. No nonzero-\(h\) formula is asserted
here. Rank three by itself does not separate older weak-output directions
from this new image. The following sections retain the same actual binary
correction and resolve one such two-layer quotient.

## The entire first weak image

The preceding three columns describe the whole first weak image on the
exact binary kernel. Regard the \(6k\) completed columns as a formal
coefficient space, and let \(\mathcal K_k\) be the subspace with exact
row sum zero and zero completed binary limit. The row-sum map has rank
two, with image \(\operatorname{span}\{1,r\}\). On its kernel, the
binary map has rank \(3k\) by (SL34). Therefore

\[
 \dim\mathcal K_k=3k-2,\qquad
 \dim\mathcal K_{k-1}=3k-5\quad(k\ge3).
 \tag{BW15}
\]

Appending the last kernel embeds the shorter formal coefficient space
and sends \(\mathcal K_{k-1}\) into \(\mathcal K_k\). Its first weak
output is zero by (BW10). The three columns (BW8) are independent modulo
this inherited subspace: their terminal coefficients on
\(C^J_{k0},C^J_{k1},Z_k\) are independent. The dimension difference is
exactly three. Consequently the entire first weak image is

\[
 \mathcal N_k=\Delta_k\operatorname{span}\{B_0,B_1,B_2\},\qquad
 \Delta_k=b_k\mathcal A_k-b_m\mathcal A_m,
 \qquad\dim\mathcal N_k=3.
 \tag{BW16}
\]

This dimension argument concerns formal coefficients and the explicitly
proved binary map. It assumes no independence of the original paired
family. By (BW6), every member of \(\mathcal N_k\) vanishes at zero and
at infinity for \(k\ge3\).

## An explicit next-layer transfer

Let an actual shorter completed combination have exact row sum zero and
expansion \(C=\delta q+O(\delta^2)\), with
\(q_2=rc\). For the moment assume \(c(\infty)=0\). Its poles are
simple old poles: the leading completed row is identically zero, so a
moving-pole derivative cannot create a double pole at this first
nonzero coefficient. The same canceled-coordinate factors give
\(q_1(0)=q_2(0)=0\); the output-0 column is bounded at infinity, so
\(q_1+q_2=-q_0\in\mathcal B_m\).

Write

\[
 e_k=\frac{-Ar}{(2-Ar)(1-Ar)},\quad
 Q_k=-\frac{r(2-Ar)}{3(1-Ar)},\quad
 \chi_k=\frac{4b_kr}{3(1-Ar)},\quad \xi=1/A.
 \tag{BW17}
\]

The first binary error after appending \(K_k\) is
\(g=d_kq_1+e_kq_2\). Subtract the appended binary lift of
\(q_1+q_2\). The remaining error is exactly

\[
 g'= (e_k-d_k)rc=d_kQ_kc.
 \tag{BW18}
\]

Set \(\lambda=c(\xi)/D_o(\xi)\). Choose the terminal part of a lift
of \(g'\) to be \(\lambda Z_k\). Its shorter inherited part has scalar

\[
 f=Q_k(c-\lambda D_o)\in\mathcal B_m.
 \tag{BW19}
\]

The new state-2 pole cancels by the choice of \(\lambda\), the function
vanishes at zero, and it is bounded at infinity because
\(c(\infty)=D_o(\infty)=0\). Thus (BW4) supplies an actual shorter
lift, with the same coefficients used in the correction of the full
completed row.

Subtract \(\delta\) times this combined binary lift from \(CK_k\).
The new completed row starts at order \(\delta^2\). Its output-2
coefficient at that order, divided by \(X_2=r\), is

\[
 \boxed{\mathscr T_k(c)
   =\chi_k c-\Delta_k\frac{c(\xi)}{D_o(\xi)}D_od_kQ_k.}
 \tag{BW20}
\]

Indeed, the terminal identity gives
\([\delta]\eta_k=-rb_k\mathcal A_k\) and
\([\delta]\chi=\chi_k\). The common \(\eta_k\) term cancels with
the same binary lift. Its sole remaining terminal defect is the second
term of (BW20). Changing the chosen binary lift changes this expression
by a member of \(\mathcal N_k\), by (BW16). This is therefore an actual
coefficient-level transfer modulo the new first weak image.

## Its exact one-dimensional kernel and a two-layer separation

Consider (BW20) on scalars with simple old poles, regular at zero,
bounded at infinity, and value zero at infinity. Impose the additional
generic unit conditions

\[
 \Delta_k(2/A)\ne0,\qquad \Delta_k(1/(2A))\ne0,\qquad
 \frac{4b_k}{3}+\Delta_k(\xi)\ne0.
 \tag{BW21}
\]

These are genuine open conditions on the positive table parameters.
The space \(\mathcal N_k\) has no new state-2 pole. Multiplying (BW20)
by \(1-Ar\) and evaluating at \(\xi\) gives

\[
 \left.(1-Ar)\mathscr T_k(c)\right|_{r=\xi}
       =\frac{c(\xi)}A
                    \left(\frac{4b_k}{3}+\Delta_k(\xi)\right).
 \tag{BW22}
\]

Thus \(\mathscr T_k(c)\in\mathcal N_k\) forces \(c(\xi)=0\).
It then reduces to \(\mathscr T_k(c)=\chi_kc\). Since \(c\) has no
new state-0 or state-1 pole, the exclusive state-0 pivot in (BW6)
must vanish. The two remaining numerator linear forms in (BW12) span
all linear polynomials; cancellation of their state-1 pole leaves
precisely the line
\(\operatorname{span}\{\Delta_kD_or^2/(1-a_1r)\}\).
It follows in both directions that

\[
 \ker(\mathscr T_k\bmod\mathcal N_k)
       =\operatorname{span}\{\psi_k\},\qquad
 \psi_k=\frac{D_o}{1-a_1r}
       \left((b_k-b_m)r+\frac{b_k}{A}-\frac{b_m}{a_m}\right)(1-Ar).
 \tag{BW23}
\]

For the converse, \(\psi_k(\xi)=0\) and
\(\chi_k\psi_k=4b_k\Delta_kD_or^2/(1-a_1r)\in\mathcal N_k\).

Now let \(m\ge3\) and restrict to the actual first weak image
\(\mathcal N_m\). Every such function contains the factor
\(\Delta_m=b_m\mathcal A_m-b_{m-1}\mathcal A_{m-1}\). Generically this
factor has a finite nonzero root \(\zeta\), off all relevant poles,
and every member of \(\mathcal N_m\) vanishes at \(\zeta\).
For generic new \(A,b_k\), \(\psi_k(\zeta)\ne0\). In fact the
coefficient of the free parameter \(b_k\) in its parenthesis is
\(\zeta+1/A\), which is nonzero away from one further proper condition.
Therefore

\[
 \mathcal N_m\cap\operatorname{span}\{\psi_k\}=0,
 \qquad
 \mathscr T_k:\mathcal N_m\longrightarrow
       \mathcal S_k/\mathcal N_k\quad\text{is injective generically}.
 \tag{BW24}
\]

All conditions can be intersected within the same positive parameter
family. This proves separation of the transported old first weak image
from the new first weak image, with the actual scalar correction retained.
It does not yet iterate through every older graded image. In particular,
the \(m=2\) oldest weak layer can have nonzero value at infinity and
must not be inserted into (BW19) without an additional correction.

## The bounded-at-infinity extension

The additional correction is explicit, and does not enlarge the generic
kernel in (BW23). Allow \(c\) to be bounded at infinity with arbitrary
\(c_\infty\). Use the actual zero-row-sum head difference

\[
 \mathcal H_k=C^H_{k1}-C^H_{11},\qquad
 B_H=(\mathcal H_k|_0)_1=-rD_od_k\Lambda_k,
 \qquad B_H(\infty)=\frac{a_m-A}{2a_mA}.
 \tag{BW25}
\]

There is no new state-2 pole in \(B_H/d_k\). At zero this quotient is
\(O(r)\), while its linear coefficient at infinity is
\((A-a_m)/(3a_m)\). Consequently set

\[
 \alpha(c)=-\frac{a_m}{A-a_m}c_\infty,\qquad
 \lambda=\frac{c(\xi)}{D_o(\xi)},\qquad
 f=Q_k(c-\lambda D_o)-\alpha(c)\frac{B_H}{d_k}
       \in\mathcal B_m.
 \tag{BW26}
\]

The coefficient \(\alpha\) cancels the linear growth at infinity. The
state-2 cancellation and the zero value at the origin are unchanged.
The actual binary lift of \(d_kQ_kc\) now consists of the terminal
terms \(\lambda Z_k+\alpha\mathcal H_k\) and the appended shorter
lift of \(f\).

The terminal part of \(\mathcal H_k\) is \(C^H_{k1}\). Write
\(B_{\rm new}=-r(P_k|_{\delta=0})_{11}=-r p_{k,1}\) for its binary
output. Its precise weak
defect relative to words ending in \(K_k\) is

\[
 W_H=\left.\frac{(\mathcal H_k)_2}{\delta X_2}\right|_0
                         +b_k\mathcal A_kB_H
       =\Delta_kB_{\rm new}+\frac{b_k-b_m}{3}r.
 \tag{BW27}
\]

The last polynomial term is required: the two constituent head row sums
are \(-r\) and \(+r\), and their terminal indices differ. The linear
growth in the displayed right side cancels, so it is bounded at infinity.
The corrected transfer is therefore

\[
 \mathscr T_k^\infty(c)
      =\chi_kc-\Delta_k\lambda D_od_kQ_k-\alpha(c)W_H.
 \tag{BW28}
\]

As the actual moved-first word ends in \(m\),
\(B_{\rm new}=-r-1/(2a_m)+O(r^{-1})\). Substitution gives the exact
infinity values

\[
 \begin{split}
 W_H(\infty)&=\frac{b_m}{2a_m}-\frac{b_k}{6a_m}-\frac{b_k}{3A},\\
 \mathscr T_k^\infty(c)(\infty)
      &=\frac{A b_m-(3A-2a_m)b_k}{2A(A-a_m)}c_\infty.
 \end{split}
 \tag{BW29}
\]

Impose the further generic condition that the numerator in (BW29) is
nonzero. Since every member of \(\mathcal N_k\) vanishes at infinity,
\(\mathscr T_k^\infty(c)\in\mathcal N_k\) forces \(c_\infty=0\).
Then \(\alpha=0\), and the previous calculation applies without change:

\[
 \ker(\mathscr T_k^\infty\bmod\mathcal N_k)
                     =\operatorname{span}\{\psi_k\}.
 \tag{BW30}
\]

This isolates the oldest layer's infinity contribution using an actual
head difference. It does not prove that its remaining finite part, or
every later transported image, avoids \(\psi_k\).

The new-parameter dependence of that obstruction is particularly small:

\[
 \psi_k=\frac{D_o}{1-a_1r}
  \left[\left(\frac{b_k}{A}-\frac{b_m}{a_m}\right)
      +b_m\left(\frac A{a_m}-1\right)r-A(b_k-b_m)r^2\right].
 \tag{BW31}
\]

Thus varying the new parameters moves the possible kernel inside the
fixed three-dimensional shorter scalar space
\(D_o(1-a_1r)^{-1}\operatorname{span}\{1,r,r^2\}\).
New-parameter freedom alone is not an argument that it avoids every
older actual graded image. The two-layer separation (BW24) uses the
specific, proved \(\Delta_m\) divisor of the first weak image.

## The normalized accumulated image saturates

The following result concerns the boundary \(h=0\). Put

\[
 P_m=\frac{D_m}{1-a_1r},\qquad
 L_k=(b_k-b_m)r+\frac{b_k}{A}-\frac{b_m}{a_m},
 \qquad k=m+1, A=a_k, a=a_1.
 \tag{BW32}
\]

Here \(P_m\) is a scalar normalization, not an ordered kernel word.
From (BW6), (BW12), and \(\Delta_k=L_k/(3r)\), the normalized new
image is exactly

\[
 \widehat{\mathcal N}_k:=P_k^{-1}\mathcal N_k
 =\frac{L_k}{r}\operatorname{span}\{
 (2-ar)(1-2Ar),\ r(2-Ar),\ r^2(2-Ar)\}.
 \tag{BW33}
\]

Nonzero parameter constants have been absorbed into the three generators.
Generically its first generator has a nonzero \(r^{-1}\) coefficient,
its third has a nonzero cubic coefficient, and its second is a nonzero
quadratic polynomial. These two extreme coefficient functionals are
independent, so
\(\dim(\widehat{\mathcal N}_k\cap\mathbb P_2)=1\).

Writing \(c=P_m g\), the exact normalized transfer (BW20) is

\[
 \boxed{\mathscr R_k g
 =\frac{2-Ar}{9(1-Ar)}
 \left[-\frac{4b_k}{A}(1-2Ar)g(r)
       +\frac{L_k(r)(1-ar)}{1-a/A}g(1/A)\right].}
 \tag{BW34}
\]

Its kernel modulo \(\widehat{\mathcal N}_k\) is the line
\(\operatorname{span}\{L_k(1-Ar)\}\). It introduces at most one
new simple pole, at \(1/A\). Its coefficient there is nonzero times
\(g(1/A)\), under (BW21). If \(g\) has polynomial degree at least
two, the first term raises that degree by one with leading multiplier
\(8b_k/9\); the evaluation term has polynomial degree at most two.
Its minimum Laurent exponent remains at least \(-1\).

Define the accumulated scalar images, over the rational parameter field,
by the actual transfer:

\[
 \mathscr S_3=\widehat{\mathcal N}_3,\qquad
 \mathscr S_k=\widehat{\mathcal N}_k+\mathscr R_k\mathscr S_{k-1}.
 \tag{BW35}
\]

These spaces combine weak coefficients born at different prefixes; their
different powers of \(\delta\) are restored below. They are contained in

\[
 \mathscr V_m=\operatorname{span}\{r^{-1},1,r,\ldots,r^m\}
       \oplus\operatorname{span}
          \{(r-1/a_j)^{-1}:4\le j\le m\},
 \qquad \dim\mathscr V_m=2m-1.
 \tag{BW36}
\]

The displayed poles are distinct, so this dimension is exact. Conversely,
\(P_m\mathscr V_m\) has only simple old poles, is regular at zero,
and vanishes at infinity. Thus the domain conditions for (BW20) continue
to hold throughout this recurrence.

The generic dimensions are

\[
 \boxed{\dim\mathscr S_3=3,\quad \dim\mathscr S_4=6,
 \quad \mathscr S_m=\mathscr V_m\quad(m\ge5).}
 \tag{BW37}
\]

Here is the step that prevents a dimension-only inference. The two-layer
result (BW24) gives \(\dim\mathscr S_4=6\). If
\(p=n+\mathscr R_4g\in\mathbb P_2\), with
\(n\in\widehat{\mathcal N}_4\) and
\(g\in\widehat{\mathcal N}_3\), the new pole forces
\(g(1/a_4)=0\). Its degree-four coefficient forces the cubic coefficient
of \(g\) to vanish. These are two independent conditions on the
three-dimensional \(\widehat{\mathcal N}_3\): after its unique cubic
direction is removed, evaluation at the free generic point \(1/a_4\)
is nonzero on its nonzero polynomial generator. Hence the possible
\(g\)'s have dimension at most one. For each such \(g\), cancellation
of the \(r^{-1}\) and cubic coefficients leaves at most one free
direction in \(n\), by the independent extremes in (BW33). Therefore

\[
 \dim(\mathscr S_4\cap\mathbb P_2)\le2.
\]

The reverse inequality follows inside the seven-dimensional
\(\mathscr V_4\), since \(\dim\mathscr S_4=6\) and
\(\dim\mathbb P_2=3\). Thus this intersection has exactly dimension
two; in particular, \(\mathscr S_4\) does not contain \(\mathbb P_2\).

For fixed old parameters the exceptional polynomials
\(L_5(1-a_5r)\), as \(a_5,b_5\) vary, span \(\mathbb P_2\).
Indeed the coefficient of \(b_5\) is \(1/a_5-a_5r^2\). A linear
functional annihilating it for every \(a_5\) must kill both the constant
and quadratic coefficients. The remaining \(b_4\) term has nonzero
linear coefficient for \(a_5\ne a_4\), so that functional is zero.
Consequently the exceptional line misses \(\mathscr S_4\) generically.
Equation (BW23) now gives
\(\dim\mathscr S_5=6+3=9=\dim\mathscr V_5\).
For every subsequent step, \(\mathbb P_2\subset\mathscr V_{k-1}\),
so the exceptional line is present and the exact quotient kernel has
dimension one. The dimension therefore increases by two, proving (BW37)
inductively. All the required nonzero rational conditions intersect a
generic open set in the positive parameter family.

Thus at the sixth block the twelve transported first-weak directions
born at prefixes \(3,4,5,6\) span only eleven scalar directions. The
three-new-directions-per-step separation cannot persist at this boundary.

## What this dependence implies for the actual determinant

The dependence is not caused by discarding unknown higher coefficients
of an actual completed column. Suppose such a column has exact row sum
zero and

\[
 C=\delta^s q+\delta^{s+1}q_{\rm next}+\cdots,\qquad s\ge1.
\]

Append \(K_k\) and subtract \(\delta^s\) times the actual binary lift
of \((qK_k^0)_1\), using the specific lift in (BW18)--(BW20). The
result starts at order \(\delta^{s+1}\), and its weak output there is
determined by

\[
 qK_k^1e_2-(\text{binary lift})^1e_2.
 \tag{BW38}
\]

There is no missing contribution from \(q_{\rm next}\), because
\(K_k^0e_2=0\) identically. Equation (BW38), divided by \(r\), is
exactly \(\mathscr T_k(c)\), where \(q_2=rc\). Changing a lift adds
a member of \(\mathcal N_k\), which is already included in (BW35).
All corrections use the same actual coefficients in every output.

More explicitly, use the nested actual coefficient kernels from
(SF3)--(SF8) of
[SOURCE24_SMALL_TIME_FILTRATION.md](SOURCE24_SMALL_TIME_FILTRATION.md).
Choose the three explicit new kernel vectors (BW8) at every prefix
\(n\ge3\), and the four origin-2 vectors. Apply the order-raising
correction through the final prefix \(m\), rather than stopping two
blocks earlier. Every correction starts at positive \(\delta\) order,
so the resulting coefficient basis still has unit determinant. An
origin-\(n\) column has completed row
\(\delta^{m-n+1}q+O(\delta^{m-n+2})\). In the actual residue matrix
whose lower output is divided by \(\delta\), factor
\(\delta^{m-n}\) from that column. Its leading upper output is zero,
and its leading lower output is the residue vector of \(-q_2=-rc\).
Moving-node residue evaluation gives the same leading coefficient,
because the divided completed row is regular in the formal parameter
over a common simple-pole denominator.

At \(m=6\), the extracted factors have total degree

\[
 4(6-2)+3\bigl((6-3)+(6-4)+(6-5)\bigr)=34.
 \tag{BW39}
\]

The twelve normalized origin-3 through origin-6 columns have leading
upper output zero and lower outputs drawn from
\(P_6\mathscr S_6\), of dimension eleven by (BW37). They are
therefore linearly dependent in the leading residue matrix, irrespective
of the other columns. It follows that

\[
 \boxed{[\delta^{34}]\det B_6(0,\delta)=0,
 \qquad \operatorname{ord}_{\delta}\det B_6(0,\delta)\ge35.}
 \tag{BW40}
\]

The order is understood as infinity if the determinant is identically
zero. This is a generic rational coefficient identity, not a finite
experiment or a nonvanishing statement.

The matrix in (SF1) is jointly analytic in \(h,\delta\), and its
determinant is divisible by \(\delta^{34}\) before setting \(h=0\).
Combining that divisibility with (BW40) gives only

\[
 \boxed{\operatorname{ord}_{\epsilon}
       \det B_6(\epsilon,\epsilon^2)\ge69.}
 \tag{BW41}
\]

Indeed the coefficient of \(\delta^{34}\) vanishes at \(h=0\),
so it is divisible by \(h\); it need not be divisible by \(h^2\).
The fixed Laurent lower bound in (BW36) is specific to \(h=0\),
and this proof does not extend (BW37) to generic \(h\). It therefore
does not prove diagonal order at least 70, determine the exact order,
or prove nonzero paired/source determinants.

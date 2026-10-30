# Scalar Laurent spanning for the first completed-output coefficient

Status: audited paper proof. The formulas, spanning arguments, and final text
have passed local and independent review. This is not a Lean theorem.
It proves a scalar-span statement, not independence in the later-column
quotient or independence of the paired/source family.

This resolves the shorter scalar-span question left after (LC195) in
[SOURCE24_LAST_TIME_COALESCENCE.md](SOURCE24_LAST_TIME_COALESCENCE.md).
The common-tail observation there is faithful on the scalar ambient; its
interaction with the later actual columns remains a separate question.

## Actual columns and the scalar ambient

Fix

\[
 G=I+\mathbf1\mathbf1^T
   =\begin{pmatrix}2&1&1\\1&2&1\\1&1&2\end{pmatrix},\qquad
 X=(1,-r,r-2h),\qquad v=(2h,-r,r-2h).
 \tag{SL1}
\]

The old tables are \(A_t=G\operatorname{diag}(1,a_t,b_t\delta)\), with
\(K_t=\operatorname{diag}(A_tX)^{-1}A_t\operatorname{diag}X\).
Here \(h\) and \(\delta\) are independent parameters. We prove the statement
at \(h=0\), for every \(k\ge3\), distinct \(a_t\in(1,2)\), and
\(b_t\ne0\). Positive \(b_t\) are permitted. Write

\[
 P_s=K_sK_1\cdots\widehat K_s\cdots K_k,\qquad
 P^t=K_1\cdots\widehat K_t\cdots K_k.
 \tag{SL2}
\]

Thus the distinguished factor is moved first, and every other factor remains
in increasing order. Define

\[
 \ell(s)=\begin{cases}k&s<k,\\k-1&s=k,\end{cases}\qquad
 \rho(t)=\begin{cases}2&t=1,\\1&t>1.\end{cases}
 \tag{SL3}
\]

The last factor of both \(P_s\) and \(P^s\) is \(K_{\ell(s)}\); the first
factor of \(P^t\) is \(K_{\rho(t)}\). The actual paired columns, with the
constant new-head row factors already divided out, are

\[
 H_{sb}=X_be_b(I-P_s),\qquad J_{tc}=-\mu_{tc}vP^t,
 \qquad
 (\mu_{t0},\mu_{t1},\mu_{t2})
   =\left(\frac2{L_{t0}},\frac{-r}{L_{t1}},
                    \frac{r-2h}{L_{t2}}\right),
 \quad L_{ta}=(A_tX)_a.
 \tag{SL4}
\]

Retain their completed parts, including their actual prefactors:

\[
 C^H_{sb}=X_be_bP_s,\qquad C^J_{tc}=\mu_{tc}vP^t,
 \qquad
 F_{sb}=\left.\frac{(C^H_{sb})_2}{\delta X_2}\right|_{\delta=0,h=0},
 \quad
 I_{tc}=\left.\frac{(C^J_{tc})_2}{\delta X_2}\right|_{\delta=0,h=0}.
 \tag{SL5}
\]

In particular, \(H_{sb}=X_be_b-C^H_{sb}\) and \(J_{tc}=-C^J_{tc}\).
Every nonempty word's final output 2 is divisible by \(\delta X_2\).
Cancel this factor before specialization, rather than evaluating an
uncanceled quotient at \(r=0\) or \(\delta=0\).

Put

\[
 l_{t0}=2-a_tr,\qquad l_{t1}=1-2a_tr,\qquad l_{t2}=1-a_tr.
 \tag{SL6}
\]

All \(3k\) roots of these forms are distinct: the three types lie in
\((1,2)\), \((1/4,1/2)\), and \((1/2,1)\), respectively.
The scalar ambient \(\mathcal S_k\) consists of rational functions with
at most simple poles at these roots and bounded at infinity. Its dimension
is \(3k+1\). The functions in (SL5) belong to it. Equivalently, the
undivided coefficient \(c=(C_2/\delta)|_0=rF\) has polynomial part of
degree at most one and vanishes at \(r=0\), as required in (LC195).

**Claim.** For \(k\ge3\), the actual completed scalars in (SL5) span
\(\mathcal S_k\).

## Binary reduction and the exact terminal cancellation

At \(\delta=0\),

\[
 K_t^0=\begin{pmatrix}
 2/l_{t0}&-a_tr/l_{t0}&0\\
 1/l_{t1}&-2a_tr/l_{t1}&0\\
 1/l_{t2}&-a_tr/l_{t2}&0
 \end{pmatrix}.
 \tag{SL7}
\]

Define the active determinant, affine intercept, and row-2 difference by

\[
 d_t=\frac{-3a_tr}{l_{t0}l_{t1}},\qquad
 f_t=\frac{-a_tr}{l_{t0}},\qquad
 e_t=\frac{-a_tr}{l_{t0}l_{t2}},\qquad D=\prod_{t=1}^k d_t.
 \tag{SL8}
\]

For a row with sum one, output 2 zero, and output-1 coordinate \(p\), the active binary
update is \(p\mapsto f_t+d_tp\). If \(p_{s,b}=(P_s^0)_{b1}\), this gives

\[
 p_{s,1}=p_{s,0}+D,\qquad p_{s,2}=p_{s,0}+D\frac{e_s}{d_s}.
 \tag{SL9}
\]

The needed terminal identity is exact before taking the limit. For a kernel
with weighted coordinates \((1,y,z)\),

\[
 Ke_2=\frac z{3+z}\mathbf1
       +\frac{z(1-y)}{y(3+z)}Ke_1
       +\frac{4z}{(3+z)(1+y+2z)}e_2.
 \tag{SL10}
\]

For a word of length at least two, its prefix output 2 is \(O(\delta)\).
The last term of (SL10), applied to that prefix, is therefore
\(O(\delta^2)\). With

\[
 A_l=\frac{1+a_lr}{3a_lr},\qquad
 Q_s=-r+r\frac{e_s}{d_s}=-\frac{r l_{s0}}{3l_{s2}},
 \tag{SL11}
\]

we obtain the first completed-output coefficient

\[
 \left.\frac{(P_s)_{b2}}{\delta X_2}\right|_0
     =b_{\ell(s)}\left(\frac13-A_{\ell(s)}p_{s,b}\right).
 \tag{SL12}
\]

Consequently

\[
 \begin{split}
 F_{s1}&=-rF_{s0}+r b_{\ell(s)}A_{\ell(s)}D,\\
 F_{s2}&= rF_{s0}-r b_{\ell(s)}A_{\ell(s)}D\frac{e_s}{d_s},\\
 G_s:=F_{s1}+F_{s2},\qquad
 \frac{G_s}{D}&=-b_{\ell(s)}A_{\ell(s)}Q_s.
 \end{split}
 \tag{SL13}
\]

For the incoming word, \(vP^t\) has row sum zero and leading output 1
equal to \((D/d_t)Q_{\rho(t)}\). Since \(k-1\ge2\), its terminal
identity has the same cancellation as (SL12). Thus

\[
 \frac{I_{tc}}D
   =-\mu_{tc}^0 b_{\ell(t)}A_{\ell(t)}\frac{Q_{\rho(t)}}{d_t},
 \qquad
 \frac{I_{t0}}D
   =\frac{2b_{\ell(t)}}{3a_t}A_{\ell(t)}Q_{\rho(t)}
                    \left(\frac1r-2a_t\right).
 \tag{SL14}
\]

The superscript on \(\mu^0\) means specialization after cancellation.
Only incoming state 0 is used below. For \(k=2\), an omitted word has
length one and its initial state-2 term in (SL10) survives. The proof and
claim here do not cover that case.

## The state-2 poles and two central Laurent directions

Multiplication by \(D^{-1}\) is an invertible linear map on rational
functions. It takes \(\mathcal S_k\) to the space consisting of Laurent
polynomials with powers \(-k,\ldots,k\), together with simple poles at the
\(k\) state-2 nodes \(r=1/a_s\). There are no remaining active-node poles.
This space again has dimension \((2k+1)+k\).

By (SL13), \(G_s/D\) has only its own state-2 pole, with nonzero residue.
Thus the \(k\) head sums provide independent pivots at all state-2 nodes.

For \(t=1,2\), the last index is \(k\). Use the actual constant-coefficient
combination

\[
 \widehat I_{t0}=I_{t0}
       +\frac{2(a_{\rho(t)}-2a_t)}{3a_t}G_{\rho(t)}.
 \tag{SL15}
\]

Substitution in (SL13)–(SL14) cancels its sole state-2 pole and gives

\[
 \frac{\widehat I_{t0}}D
      =-\frac{2b_k}{9a_t}A_k l_{\rho(t),0}.
 \tag{SL16}
\]

Because \(a_1\ne a_2\), the two linear forms \(2-a_1r,2-a_2r\) span
\(1,r\). The cleaned actual span therefore contains \(A_k\) and \(rA_k\).

## Actual moved-first differences

Use the following Laurent factors, distinguished from the matrix words:

\[
 p_t=d_t^{-1}=\frac53-\frac23\left(a_tr+\frac1{a_tr}\right),
 \qquad q_t=f_t/d_t=\frac{1-2a_tr}{3},
 \qquad
 \mathscr P_j=\prod_{i\le j}p_i,\quad
 \mathscr Q_j=\sum_{i\le j}q_i\prod_{l<i}p_l.
 \tag{SL17}
\]

The affine recursion gives \(p_{1,0}/D=\mathscr Q_k\). For
\(2\le s\le k-1\), define the actual moved-first difference
\(\Lambda_s=(p_{s,0}-p_{1,0})/D\). Its common suffix cancels exactly,
leaving

\[
 \Lambda_s=(p_s-1)\mathscr Q_{s-1}
                      +(1-\mathscr P_{s-1})q_s.
 \tag{SL18}
\]

It has support in \([1-s,s-1]\), with outer coefficients

\[
 \begin{split}
 [r^{1-s}]\Lambda_s
   &=\frac12\left(-\frac23\right)^s
            \frac{a_s-a_{s-1}}{\prod_{j\le s}a_j},\\
 [r^{s-1}]\Lambda_s
   &=\frac12\left(-\frac23\right)^s
            (a_s-a_{s-1})\prod_{j\le s-2}a_j.
 \end{split}
 \tag{SL19}
\]

These follow by inserting (SL17) into (SL18). For the upper coefficient,
the potential degree-\(s\) terms cancel; equivalently, the affine output of
a word of length at least two ending at \(t\) is
\(1+(2a_tr)^{-1}+O(r^{-2})\) at infinity.
For the lower coefficient, use the leading \(r^{-1}\) coefficient of each
\(p_j\) and the constant coefficient \(1/3\) of \(q_j\). As a direct
initial check,

\[
 \Lambda_2=\frac29(a_2-a_1)
   \left(r-\frac{2(a_1+a_2)}{a_1a_2}+\frac1{a_1a_2r}\right).
 \tag{SL20}
\]

For each \(s\), the lowest power of \(\Lambda_s\) and the highest power
of \(r\Lambda_s\) are new relative to earlier indices. Hence

\[
 1,r,\Lambda_2,r\Lambda_2,\ldots,
                    \Lambda_{k-1},r\Lambda_{k-1}
 \tag{SL21}
\]

is a basis of Laurent polynomials supported on \([2-k,k-1]\).
All these directions arise from actual columns: (SL16) supplies the first
two after multiplication by \(A_k\), and

\[
 \frac{F_{s0}-F_{10}}{b_kD}=-A_k\Lambda_s,
 \qquad
 \frac{F_{s1}-F_{11}}{b_kD}=rA_k\Lambda_s
       \quad(2\le s\le k-1).
 \tag{SL22}
\]

Multiplication by \(A_k=(r+1/a_k)/(3r)\) identifies their span with the
codimension-one subspace of Laurent polynomials on \([1-k,k-1]\)
that vanish at \(r_*=-1/a_k\).

## The terminal incoming exception and the two outer powers

The omitted-last incoming word is essential. By (SL14),

\[
 \frac{I_{k0}}D
   =\frac{2b_{k-1}}{3a_k}A_{k-1}Q_1
                   \left(\frac1r-2a_k\right).
 \tag{SL23}
\]

Put \(r_1=1/a_1\) and define the effect-constant residue ratio

\[
 c_*=-\frac{2b_{k-1}}{3a_kb_k}
       \frac{A_{k-1}(r_1)}{A_k(r_1)}(a_1-2a_k),
 \qquad \widehat I_{k0}=I_{k0}-c_*G_1.
 \tag{SL24}
\]

The state-2 pole cancels. The remaining function
\(\widehat I_{k0}/D\) is Laurent on \([-1,1]\), which is contained in
\([1-k,k-1]\). Since \(G_1/D\) vanishes at \(r_*\),

\[
 \frac{\widehat I_{k0}}D(r_*)
      =-2b_{k-1}A_{k-1}(r_*)Q_1(r_*)\ne0.
 \tag{SL25}
\]

Here \(a_{k-1}\ne a_k\) makes \(A_{k-1}(r_*)\ne0\), and positivity
of the \(a_t\) makes \(Q_1(r_*)\ne0\). This adds the missing central
direction, so the cleaned span contains every Laurent polynomial on
\([1-k,k-1]\).

Finally, the two base heads supply the two outer powers. Exactly,

\[
 \frac{F_{10}}{b_kD}=\frac{\mathscr P_k}{3}-A_k\mathscr Q_k,
 \qquad
 \frac{F_{11}}{b_kD}=-r\frac{F_{10}}{b_kD}+rA_k.
 \tag{SL26}
\]

The first function has support \([-k,k-1]\), the second
\([1-k,k]\), and

\[
 [r^{-k}]\frac{F_{10}}{b_kD}
    =\frac12\left(-\frac23\right)^k\frac1{\prod_ta_t},
 \qquad
 [r^k]\frac{F_{11}}{b_kD}
    =\left(-\frac23\right)^k\frac{\prod_ta_t}{2a_k}.
 \tag{SL27}
\]

Both are nonzero. For the first formula, the completed row-0 output
coefficient tends to \(b_k/2\) at zero. For the second, the completed
row-1 coefficient, including \(X_1=-r\), tends to \(b_k/(2a_k)\) at
infinity. Equivalently, (SL26) shows the canceled top power of its first
function explicitly. Thus these are two successive pivots, not merely
two vectors outside the central space.

The complete Laurent part \([-k,k]\) is now present, together with the
\(k\) independent state-2 pole pivots. This proves the claim.

## Actual basis, generic continuation, and scope

A concrete basis after constant column operations consists of:

- the \(k\) head sums \(G_s\);
- the \(2k-4\) head differences in (SL22);
- the three cleaned incoming columns with \(t=1,2,k\), all state 0;
- the two base heads \(F_{10},F_{11}\).

Their total is \(k+(2k-4)+3+2=3k+1\). Every change of columns uses
coefficients depending only on table parameters, never on \(r\). In
particular, the proof does not assume closure under multiplication by
the effect coordinate.

The coefficient functions are rational and regular in \(h\) near zero
after the displayed cancellation of \(\delta X_2\). A nonzero scalar
minor at \(h=0\) therefore persists for generic sufficiently small
positive \(h\). This is a nonvanishing argument for the scalar family;
the boundary value \(h=0\) itself is not a positive new-time instance.

Multiplying back by \(X_2\) gives the full \(3k+1\)-dimensional
completed-output scalar space used in (LC195). It identifies the rank
of that faithful common-tail scalar observation before quotienting by
later source columns. It does not establish that those directions
survive the later-column correction, does not prove a paired determinant
nonzero, and does not prove Eq. (24).

## Binary completed-output lifts with exactly zero row sum

There is a separate consequence using the leading output 1, rather than
the first output-2 coefficient. It holds for every \(k\ge2\), including
\(k=2\). Retain the actual completed rows in (SL5). For an
effect-constant coefficient vector \(\gamma\), write \(C(\gamma)\) for
its completed row combination and impose the exact condition

\[
 s(\gamma):=C(\gamma)\mathbf1
       =\sum_{s,b}\gamma^H_{sb}X_b\equiv0.
 \tag{SL28}
\]

Every incoming completed row already has row sum zero. This condition is
on the scalar row-sum function; it does not say that the polynomial head
row of the corresponding actual source combination vanishes.

At \(\delta=0\), each nonempty completed word has output 2 equal to zero.
Thus a combination satisfying (SL28) has the binary form
\((-g,g,0)\), where \(g=(C(\gamma)|_{\delta=0})_1\). Its scalar ambient is

\[
 \mathcal B_k=\{g:\text{at most simple poles at the }3k
       \text{ nodes in (SL6), bounded at infinity, and }g(0)=0\},
 \qquad \dim\mathcal B_k=3k.
 \tag{SL29}
\]

The factor \(X_1=-r\) in every kernel's output-1 column proves the
vanishing at zero. At infinity the output-0 column of the final binary
kernel is \(O(r^{-1})\); its input is \(O(r)\). Hence output 0 is
bounded, and zero row sum makes output 1 bounded as well. Distinct
simple old factors give the asserted pole restriction.

At \(h=0\), define the following actual completed combinations:

\[
 \begin{split}
 Z_s&=C^H_{s1}+C^H_{s2},\\
 D_{s0}&=C^H_{s0}-C^H_{10},\qquad
 D_{s1}=C^H_{s1}-C^H_{11}\quad(2\le s\le k).
 \end{split}
 \tag{SL30}
\]

All satisfy (SL28). Write \(\mathcal L(C)= (C|_{\delta=0,h=0})_1/D\).
The binary formulas above give

\[
 \mathcal L(Z_s)=Q_s,\qquad
 \mathcal L(D_{s0})=\Lambda_s,\qquad
 \mathcal L(D_{s1})=-r\Lambda_s,
 \qquad
 \mathcal L(C^J_{t0})=-\frac2{3a_t}Q_{\rho(t)}
                                   \left(\frac1r-2a_t\right).
 \tag{SL31}
\]

Here (SL18)–(SL19) now define \(\Lambda_s\) for every
\(2\le s\le k\). No last-index exception occurs in a leading output-1
formula. For \(t=1,2\), the constant-coefficient combination

\[
 \widehat C^J_{t0}=C^J_{t0}
     +\frac{2(a_{\rho(t)}-2a_t)}{3a_t}Z_{\rho(t)}
 \quad\text{satisfies}\quad
 \mathcal L(\widehat C^J_{t0})
                  =\frac2{9a_t}l_{\rho(t),0}.
 \tag{SL32}
\]

The two right sides span \(1,r\). The same distinct outer coefficients
in (SL19), now continued through \(s=k\), show that

\[
 1,r,\Lambda_2,r\Lambda_2,\ldots,\Lambda_k,r\Lambda_k
 \tag{SL33}
\]

is a basis of Laurent polynomials supported on \([1-k,k]\), of
dimension \(2k\). Each \(Q_s\) has one nonzero simple residue at its
own state-2 node and no other state-2 pole. These add \(k\) independent
directions. Multiplication by \(D\) identifies this \(3k\)-dimensional
space with \(\mathcal B_k\). Therefore

\[
 \{C(\gamma)|_{\delta=0,h=0}:s(\gamma)=0\}
       =\{(-g,g,0):g\in\mathcal B_k\}.
 \tag{SL34}
\]

A concrete lifting basis consists of the \(k\) columns \(Z_s\), the
\(2k-2\) differences \(D_{s0},D_{s1}\), and the two cleaned incoming
columns in (SL32). All coefficient changes are constant in \(r\).
Unlike (SL12)–(SL14), this proof does not discard a first output-2 term,
so an incoming word of length one causes no exception at \(k=2\).

For continuation to nonzero \(h\), replace only the head sums by

\[
 Z_s(h)=2hC^H_{s0}+C^H_{s1}+C^H_{s2}.
 \tag{SL35}
\]

Their row sum is exactly \(2h-r+(r-2h)=0\), for every \(\delta\),
not merely to leading order. The head differences and incoming columns
already satisfy (SL28) for every \(h\). The same fixed parameter
coefficients from (SL32) therefore give an analytic family of exact
zero-row-sum combinations. Its nonzero minor at \(h=0\) proves binary
surjectivity onto \(\mathcal B_k\) for generic sufficiently small
positive \(h\).

This supplies actual constant-coefficient lifts of binary completed
scalars while retaining their associated polynomial heads. It does not
prescribe those heads independently, establish a later-column quotient
rank, or prove paired/source independence.

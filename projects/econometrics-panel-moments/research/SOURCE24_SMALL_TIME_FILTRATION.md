# Actual binary lifts and the small-time determinant filtration

Status: audited paper proof, including independent review of the scalar lift,
the nested coefficient kernels, moving residues, and specialization. This is
not a Lean theorem. The result is a determinant valuation lower bound, not
nonvanishing of any determinant coefficient.

Use the actual columns, two independent parameters, and normalization in
[SOURCE24_SCALAR_LAURENT_SPANNING.md](SOURCE24_SCALAR_LAURENT_SPANNING.md),
(SL1)--(SL5). For \(m\) old blocks let \(B_m(h,\delta)\) observe ordinary
\(r\)-residues of output 1 and output \(2/\delta\) of the \(6m\) actual
paired columns. The source column is \(R=p-C\), where \(p\) is its
polynomial head and \(C\) its completed row. Polynomial heads are retained;
their residues are zero.

For every \(m\ge3\), on the generic distinct-pole parameter set,

\[
 \boxed{\operatorname{ord}_{\delta}\det B_m
       \ \ge\ \frac{3m^2-7m+2}{2}.}
 \tag{SF1}
\]

The order is infinity if the determinant is identically zero. Along the
original positive small-time path \(h=\epsilon,\delta=\epsilon^2\), this gives

\[
 \operatorname{ord}_{\epsilon}\det B_m(\epsilon,\epsilon^2)
       \ \ge\ 3m^2-7m+2.
 \tag{SF2}
\]

Thus the lower bounds at \(m=3,4,5\) are \(4,11,21\) in \(\delta\), or
\(8,22,42\) in \(\epsilon\). Equality is a separate question.

## The actual binary coefficient map

Work over the parameter field
\(F=\mathbb Q(h,a_1,\ldots,a_m,b_1,\ldots,b_m)\) and its formal power
series ring \(F[[\delta]]\). All coefficient vectors below are constant in
the effect coordinate \(r\); they may depend on these parameters and on
\(\delta\).

For a coefficient vector on the first \(6n\) actual columns, let \(C_n\)
be its completed row and define

\[
 s_n=C_n\mathbf1,\qquad
 f_n=(C_n|_{\delta=0})_1,\qquad
 \mathcal A_n:\gamma\longmapsto(s_n,f_n).
 \tag{SF3}
\]

The row sum \(s_n\) is an affine polynomial in \(r\), independent of
\(\delta\) for constant coefficient vectors. For \(n\ge2\), every
completed word is nonempty, including the incoming omitted word.
Consequently \(C_n|_{\delta=0}\) has output 2 zero, and \(f_n(0)=0\).
All its possible poles are the \(3n\) distinct binary row-form poles.
Its growth at infinity is at most linear. The final binary kernel's
output-0 column is \(O(1/r)\), while its input is \(O(r)\), so
\((C_n|_{\delta=0})_0\) is bounded. Hence the linear coefficients of
\(f_n\) and \(s_n\) agree.

The target of (SF3) has dimension \(3n+2\): \(f_n\) has \(3n\) simple
pole coefficients and an affine part subject to \(f_n(0)=0\), giving
\(3n+1\) dimensions; \(s_n\) adds its constant coefficient. The binary
lift theorem (SL28)--(SL35) proves surjectivity on \(s_n=0\) onto the
\(3n\)-dimensional bounded scalar space. The two head sums \(X_0=1\)
and \(X_1=-r\) give the two independent remaining polynomial sums.
Therefore

\[
 \operatorname{rank}\mathcal A_n=3n+2,\qquad
 \mathcal K_n:=\ker\mathcal A_n,\qquad
 \dim\mathcal K_n=3n-2\quad(n\ge2).
 \tag{SF4}
\]

These are kernels of actual source coefficients, not ambient row
interpolation spaces. For every old column, extending the prefix appends
the next factor on the right:

\[
 C_{n+1}(\gamma,0)=C_n(\gamma)K_{n+1}.
 \tag{SF5}
\]

Both the moved-first and omitted words have precisely this property.
A vector in \(\mathcal K_n\) has exact row sum zero and
\(C_n=O(\delta)\). Equation (SF5) therefore embeds
\(\mathcal K_n\) into \(\mathcal K_{n+1}\).
Choose nested constant bases: four vectors at \(n=2\), and three new
vectors at every later prefix.

## Raising the completed-row order with actual columns

Suppose a parameter-power-series coefficient vector \(x\) at prefix
length \(\ell\ge2\) has

\[
 s_\ell(x)=0,\qquad C_\ell(x)=O(\delta^j),\qquad j\ge1.
 \tag{SF6}
\]

Its leading quotient \(q=(\delta^{-j}C_\ell(x))|_{\delta=0}\) has
only simple old poles. To see this without differentiating moving poles,
place all completed rows over the common denominator
\(E_\ell(\delta,r)=\prod_{t\le\ell,c}L_{tc}(\delta,r)\).
Every word uses each block at most once, and an incoming prefactor uses
exactly its omitted block. Thus this common product suffices. The
numerator is divisible by \(\delta^j\); division followed by
specialization leaves denominator \(E_\ell(0,r)\), whose roots are
distinct. In particular, no repeated poles are introduced by the lift.

The row \(q\) has sum zero and growth at most linear. Appending the
binary next kernel gives

\[
 qK_{\ell+1}^0=(-g,g,0),\qquad
 g=d_{\ell+1}q_1+e_{\ell+1}q_2.
 \tag{SF7}
\]

Here \(d,e\) are (SL8). They are \(O(1/r)\) at infinity and vanish
at \(r=0\), so \(g\) is bounded at infinity and \(g(0)=0\).
The new block has disjoint simple poles; consequently \(g\) belongs
to exactly the binary scalar space \(\mathcal B_{\ell+1}\).

By the proved actual binary lift theorem, choose a coefficient vector
\(y\), constant in \(\delta\) and in \(r\), such that its completed row
has exact zero sum and binary value \((-g,g,0)\). Then

\[
 x_{\rm new}=(x,0)-\delta^j y,\qquad
 s_{\ell+1}(x_{\rm new})=0,\qquad
 C_{\ell+1}(x_{\rm new})=O(\delta^{j+1}).
 \tag{SF8}
\]

This cancels the entire leading completed row. It is stronger than
canceling a chosen residue or one scalar component. It does not set
the polynomial head row to zero.

Start an origin-\(n\) basis vector in \(\mathcal K_n\), and apply
(SF8) through prefix length \(m-2\). The resulting actual coefficient
vector satisfies

\[
 C_{m-2}=O(\delta^p),\qquad s_{m-2}=0,\qquad p=m-1-n.
 \tag{SF9}
\]

Every correction begins at positive \(\delta\) order. Thus all these
lifted vectors retain their independent nested constant coefficient
vectors, and can be extended to a full coefficient basis whose
determinant is a unit in \(F[[\delta]]\).

## The final two blocks and the determinant count

Use the last-block residue row operation from (LC189)--(LC190):

\[
 \text{lower residue}
 =\operatorname{Res}(R_2/\delta)
       -(\eta_m/\delta)(\text{node})\operatorname{Res}(R_1).
 \tag{SF10}
\]

Let \(U\) be all upper rows except the terminal state-2 row
(\(3m-1\) rows). Let \(W\) be all the lower rows plus that terminal
upper row (\(3m+1\) rows). Every ordinary earlier column has \(W=O(\delta)\);
only the six terminal columns are unrestricted.

For a lifted column (SF9), appending \(K_{m-1}\) leaves every completed
output \(O(\delta^p)\), and makes its output 2
\(O(\delta^{p+1})\). This follows from the exact zero-sum identity
\((qK)_2=\eta(qK)_1+\chi q_2\), with \(\eta,\chi=O(\delta)\).
After the final factor \(K_m\), its residue observations obey

\[
 U=O(\delta^p),\qquad W=O(\delta^{p+1}).
 \tag{SF11}
\]

At old moving poles this follows from the exact transverse identity.
At the terminal state-2 pole, only the prefix's output 2 multiplies
the singular row of \(K_m\); this gives both the special upper
bound and the transverse lower bound. At the other terminal poles
the transverse term has no residue. Denominators at distinct moving
nodes are units, so these orders survive ordinary residue evaluation.
No expansion of a multi-block tail at one of its later state-2 poles
is being interchanged with a residue.

Factor \(\delta^p\) from each lifted column. By (SF11), the remaining
earlier columns still have \(W=O(\delta)\). In every determinant term,
the \(3m+1\) rows of \(W\) can use at most the six unrestricted terminal
columns, requiring at least \(3m-5\) further factors of \(\delta\).

For \(m\ge4\), four origin-2 vectors have \(p=m-3\), and three
origin-\(n\) vectors have \(p=m-1-n\) for each \(3\le n\le m-2\).
The resulting total is

\[
 \begin{split}
 \operatorname{ord}_{\delta}\det B_m
 &\ge (3m-5)+4(m-3)+3\sum_{j=1}^{m-4}j\\
 &=\frac{3m^2-7m+2}{2}.
 \end{split}
 \tag{SF12}
\]

For \(m=3\), the earlier bound \(3m-5=4\) is already (SF1);
no origin-1 vectors are used. An incoming word at length one is empty,
so treating that prefix as another lift base would be invalid.
No invertibility assumption about six selected terminal rows is used.

## Specialization and the remaining nonvanishing problem

The constructed basis and lift coefficients may have poles at \(h=0\).
The determinant's lower \(\delta\)-coefficients nevertheless vanish
identically over \(F\). The original normalized matrix is jointly
analytic at \(h=\delta=0\) when the binary poles are distinct: the
output-2 factor was canceled before specialization and all moving-node
units persist. The vanishing coefficient identities therefore extend
to \(h=0\), and substitution \(h=\epsilon,\delta=\epsilon^2\) proves
(SF2). Regularity of the chosen coefficient basis at \(h=0\) is not
needed for this divisibility conclusion.

The four-block lower bound \(11\) in \(\delta\) is strictly larger
than the earlier first-layer bound \(3m-5=7\). Thus the finite
three-block success cannot justify a uniformly sharp first correction.

What remains is a nonzero graded determinant after these actual
coefficient corrections. The scalar bases provide lifts, but do not
prove independence of their next transverse errors modulo later
columns. Neither (SF1) nor (SF2) proves that the determinant is nonzero.

The prescribed four-block check is sharp for one exact fixture:
\(a=(5/4,3/2,7/4,15/8)\), \(b=(1,2,3,4)\), modulo 1000003,
with fixed absolute precision 25. It gives leading rank 17 and
\(\det B_4(\epsilon,\epsilon^2)=748106\epsilon^{22}
+O(\epsilon^{23})\). Its pivot valuations are seventeen zeros,
three twos, and four fours. All 576 entries of a separate rational
control match the existing actual paired evaluator. See (LC198) and
the saved script and certificate. This confirms the order bound at
that fixture, not equality or nonvanishing for arbitrary length.


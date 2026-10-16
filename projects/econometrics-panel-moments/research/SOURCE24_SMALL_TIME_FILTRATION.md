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

## Bounded weak outputs force an additional all-length defect

The following refinement is an independently audited paper argument.
Its polynomial-space observation was suggested by
[Pro research response 53](https://chatgpt.com/c/6ad1e8a7-9ac8-83ed-be7d-3d0e7e81cb59);
the actual lifting, endpoint conditions, and analytic extension were
checked locally. It is not formalized in Lean.

Put \(\nu_m=(3m^2-7m+2)/2\). Over the rational field of generic
positive table parameters, the jointly analytic determinant satisfies

\[
 \boxed{\det B_m(h,\delta)\in
        \delta^{\nu_m}(h,\delta)^{m-4}\quad(m\ge5).}
 \tag{SF13}
\]

Here the right side is an ideal in the local formal power-series ring.
In particular,

\[
 \begin{split}
 \operatorname{ord}_\delta\det B_m(0,\delta)
       &\ge \nu_m+m-4,\\
 \operatorname{ord}_\epsilon\det B_m(\epsilon,\epsilon^2)
       &\ge 2\nu_m+m-4=3m^2-6m-2.
 \end{split}
 \tag{SF14}
\]

These bounds do not assert nonvanishing or equality. They give orders
at least 43 and 70 on the diagonal path for \(m=5,6\), respectively.

First work at \(h=0\), and write \(E_n^0=\prod_{t\le n,c}l_{tc}\).
Use the actual binary scalar section (SL28)--(SL35). Suppose an exact
zero-sum completed combination is
\(C_n=\delta^j q+O(\delta^{j+1})\), and put \(w=q_2\).
Assume \(w\) is bounded at infinity. Completed output zero is bounded
there, so \(q_1=-q_0-w\) is also bounded. Both \(q_1\) and \(w\)
vanish at zero. For \(k=n+1\), set

\[
 A=a_k,\quad \xi=1/A,\quad
 M_k=r\Delta_k,\quad
 U_Z=D_nd_kQ_k,\quad
 \lambda=\frac{w(\xi)}{\xi D_n(\xi)},\quad
 f=q_1+\frac{e_k}{d_k}w-\lambda D_nQ_k.
 \tag{SF15}
\]

The only possible new pole of \(f\), at \(\xi\), cancels. Its old
poles remain simple; it is bounded at infinity and zero at the origin.
Consequently it has an actual shorter binary lift. Append that lift
and add \(\lambda Z_k\), with \(Z_k=C^H_{k1}+C^H_{k2}\).
Its binary output is exactly \((qK_k^0)_1\). Subtracting
\(\delta^j\) times this correction raises the completed-row order
by one and gives next weak output

\[
 w_{\mathrm{next}}
       =\chi_k w-\lambda M_kU_Z,\qquad
 \chi_k=\frac{4b_kr}{3(1-a_kr)}.
 \tag{SF16}
\]

This is (BW20) after replacing \(c\) by \(w/r\). It is an identity
for actual coefficients. Unknown higher coefficients contribute
nothing to this weak output because \(K_k^0e_2=0\).

At zero, \(\chi_k=O(r)\) and \(M_kU_Z=O(r^{n+2})\).
At infinity, \(\chi_k\) is bounded and
\(M_kU_Z=O(r^{1-n})\). Thus

\[
 w=O(r^n)\text{ at }0,\quad w=O(1)\text{ at infinity}
 \ \Longrightarrow\
 w_{\mathrm{next}}=O(r^{n+1})\text{ at }0,\quad
 w_{\mathrm{next}}=O(1)\text{ at infinity}.
 \tag{SF17}
\]

Every new origin-\(n\) vector from (BW8), \(n\ge3\), has
\(w=M_nB\), where its terminal binary contribution \(B\) is
\(O(r^n)\) at zero and \(O(r^{2-n})\) at infinity.
Its weak output is therefore \(O(r^n)\) at zero and bounded at infinity.

At origin two, the four-dimensional kernel also has
\(w=O(r^2)\) at zero. To see this directly, write its two
state-zero head coefficients as \(\alpha_{10},\alpha_{20}\).
The exact zero-sum condition gives
\(\alpha_{10}+\alpha_{20}=0\). The coefficient of \(r\) in its
binary first output is
\(-\tfrac12(a_2\alpha_{10}+a_1\alpha_{20})\); every other column
has order at least two. Distinct \(a_1,a_2\) force both coefficients
to be zero. The remaining head and incoming columns have weak output
of order at least two at zero, as follows directly from the last
weak column of the actual kernels. All these weak functions grow
at most linearly at infinity. Killing that one slope functional
selects at least three independent bounded origin-two vectors.

Promote these three vectors and all three new vectors at each
subsequent prefix through length \(m\), using (SF15)--(SF16).
There are \(3m-3\) such vectors. Their final weak outputs have only
the \(3m\) simple binary poles, are bounded at infinity, and vanish
to order at least \(m\) at zero. Each therefore has the form

\[
 w(r)=\frac{r^m p(r)}{E_m^0(r)},\qquad \deg p\le2m.
 \tag{SF18}
\]

This scalar space has dimension \(2m+1\). Ordinary residues are a
linear map from it, so the corresponding weak-residue columns have
rank at most \(2m+1\).

Complete the three bounded origin-two vectors to a basis of its
four-dimensional kernel, and use the nested actual kernel basis.
Promote every kernel vector all the way through \(m\). An origin-\(n\)
column then has completed order \(m-n+1\). In the residue matrix
with lower output divided by \(\delta\), extract
\(\delta^{m-n}\) from it. The extracted powers total

\[
 4(m-2)+3\sum_{n=3}^m(m-n)=\nu_m.
 \tag{SF19}
\]

Each normalized leading upper column is zero. The \(3m-3\) selected
lower columns factor through (SF18), so the remaining square matrix
has boundary rank defect at least
\((3m-3)-(2m+1)=m-4\).

For the joint ideal statement, an analytic choice of the lifting
basis is essential. The binary scalar section has a minor nonzero
at \(h=0\), by the explicit basis (SL28)--(SL35), so it extends
analytically in \(h\) near zero. The fixed-rank nested coefficient
kernels admit compatible analytic bases there. At every promotion,
extend the prescribed \(h=0\) correction in the analytic exact-zero-sum
coefficient bundle, then repair its binary error using the analytic
section. This repair vanishes at \(h=0\). The binary error is admissible:
the appended zero-sum leading row has first output bounded at
infinity, zero at the origin, and only the prescribed simple poles.
All changes beyond the initial basis carry positive powers of
\(\delta\). Hence their coefficient matrix remains a unit at
\((h,\delta)=(0,0)\).

After extracting (SF19), the resulting matrix is analytic in both
variables and has constant-term rank defect at least \(m-4\).
A constant invertible row and column change makes that many rows
zero at the origin; every determinant term then contains at least
\(m-4\) factors from the ideal \((h,\delta)\).
Multiplying back by the unit coefficient determinant proves (SF13).
Substitution gives (SF14).

The stronger six-block bound 70 uses this rank defect and analytic
lifting. It does not follow from the single vanishing coefficient
(BW40), which by itself only implies order 69. The finite order-71
certificate (LC200) is compatible with the stronger bound but does
not determine its all-parameter sharpness.


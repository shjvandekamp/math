# An explicit two-block base at the binary boundary

Status: paper proof with independently checked exact symbolic identities.
This result is not formalized in Lean. It proves invertibility of the
normalized two-block paired residue matrix at the binary boundary. It
does not supply an induction step or prove paired/source independence at
arbitrary length.

The candidate formulas came from the
[Pro54 research conversation](https://chatgpt.com/c/6ad1ea67-9660-83eb-a47d-cd9663f5605b).
The actual ordered-word identities were independently verified by
[source24_binary_two_block_symbolic.py](../exploration/source24_binary_two_block_symbolic.py);
its [saved certificate](../exploration/source24-binary-two-block-symbolic-results.json)
contains 85 successful polynomial cross-multiplications over
\(\mathbb Q(a,c,r)\). The calculation sets the common weak weight
\(\beta=1\); the dependence on arbitrary nonzero \(\beta\) is recovered
exactly by homogeneity below. No numeric choice of \(a,c\) is used.

## Actual completed rows and the limiting residue matrix

Let \(a,c\in(1,2)\) be distinct, let \(\beta\ne0\), and put

\[
 a_1=a,\qquad a_2=c,\qquad
 G=\begin{pmatrix}2&1&1\\1&2&1\\1&1&2\end{pmatrix},
 \qquad X=(1,-r,r),\qquad v=(0,-r,r).
 \tag{TB1}
\]

For \(t\in\{1,2\}\), with \(o=3-t\), define

\[
 A_t=G\operatorname{diag}(1,a_t,\beta\delta),\qquad
 L_{ti}=(A_tX)_i,\qquad
 K_t=\operatorname{diag}(L_{t0},L_{t1},L_{t2})^{-1}
                                      A_t\operatorname{diag}X.
 \tag{TB2}
\]

The actual completed rows, with their original word order, are

\[
 h_{tb}=X_be_bK_tK_o,\qquad
 j_{ti}=\mu_{ti}vK_o,\qquad
 (\mu_{t0},\mu_{t1},\mu_{t2})
       =\left(\frac2{L_{t0}},\frac{-r}{L_{t1}},\frac r{L_{t2}}\right).
 \tag{TB3}
\]

The corresponding actual source rows are \(X_be_b-h_{tb}\) and
\(-j_{ti}\). The polynomial heads \(X_be_b\) must be retained as rows,
although they contribute no ordinary residues.

Write

\[
 l_{t0}=2-a_tr,\qquad l_{t1}=1-2a_tr,\qquad
 l_{t2}=1-a_tr.
 \tag{TB4}
\]

At \(\delta=0\), the six poles are
\(2/a,1/(2a),1/a,2/c,1/(2c),1/c\). They are distinct under the stated
assumptions. The normalized limiting matrix has two observations per
pole: the ordinary \(r\)-residue of output 1, and the limit of the
ordinary residue of output 2 divided by \(\delta\). Its twelve columns
are the six \(h\)'s and six \(j\)'s. Replacing these completed columns by
the actual source columns negates every residue column, so does not
change rank.

Every completed output 2 vanishes identically at \(\delta=0\). Thus the
second observation is the ordinary residue of
\[
 w(C)=[\delta]C_2.
 \tag{TB5}
\]
The moving poles are simple and analytic in \(\delta\). Since the
zeroth output-2 rational function is zero, no derivative of a
zeroth-order residue or pole location contributes to (TB5).

## Binary surjectivity and the six-dimensional residue kernel

Let \(V\) be the twelve-dimensional formal coefficient space of (TB3),
and let \(U:V\to\mathbb R^6\) take the six binary output-1 residues.
The binary lifting theorem
[(SL28)–(SL34)](SOURCE24_SCALAR_LAURENT_SPANNING.md)
applies already at two blocks. Its specialization can be made explicit.

Put

\[
 d_t=\frac{-3a_tr}{l_{t0}l_{t1}},\qquad D=d_1d_2,\qquad
 Q_t=-\frac{r(2-a_tr)}{3(1-a_tr)}.
 \tag{TB6}
\]

The exact-zero-row-sum completed combinations

\[
 Z_t=h_{t1}+h_{t2},\qquad
 D_0=h_{20}-h_{10},\qquad D_1=h_{21}-h_{11}
 \tag{TB7}
\]

have binary output 1, after division by \(D\), respectively
\(Q_t,\Lambda,-r\Lambda\), where

\[
 \Lambda=\frac{2(c-a)}9
       \left(r+\frac1{ac\,r}-\frac{2(a+c)}{ac}\right).
 \tag{TB8}
\]

The two cleaned incoming combinations satisfy

\[
 \begin{split}
 D^{-1}\left(j_{10}+\frac{2(c-2a)}{3a}Z_2\right)_1\Big|_0
     &=\frac2{9a}(2-cr),\\
 D^{-1}\left(j_{20}+\frac{2(a-2c)}{3c}Z_1\right)_1\Big|_0
     &=\frac2{9c}(2-ar).
 \end{split}
 \tag{TB9}
\]

The right sides of (TB9) span \(1,r\). The nonzero \(r^{-1}\)
coefficient of \(\Lambda\) and \(r^2\) coefficient of \(r\Lambda\)
show that \(1,r,\Lambda,r\Lambda\) span the four Laurent powers
\(r^{-1},1,r,r^2\). Each \(Q_t\) has a nonzero residue at its own
state-2 pole and no pole at the other state-2 node, adding two
independent directions.

Multiplication by \(D\) therefore gives six independent functions in
the space \(\mathcal B_2\) of rational functions with at most simple
poles at the six nodes, bounded at infinity, and zero at \(r=0\).
This space has dimension six. Its residue map is an isomorphism:
zero residues leave a constant function, and the value at zero kills
that constant. All six functions have actual zero-row-sum lifts by
(TB7)–(TB9). Consequently

\[
 \operatorname{rank}U=6,\qquad \dim\ker U=6.
 \tag{TB10}
\]

This argument concerns formal coefficients and explicit binary rows;
it assumes no paired-matrix inverse.

## Four completed zero rows and two polynomial gauges

For an ordered pair \((t,o)\), abbreviate
\(A=a_t,\ C=a_o,\ d=A-C\). Define

\[
 \begin{split}
 \kappa_{t1}={}&j_{t1}+\frac1A h_{t1}
       +\frac{A-2C}{2Ad}h_{t2}+\frac1{2d}h_{o2}
       +\frac{A-4C}{4Cd}j_{t0}+\frac{3C}{4Ad}j_{o0},\\
 \kappa_{t2}={}&j_{t2}-\frac{2A-C}{Ad}h_{t1}
       -\frac1A h_{t2}+\frac1d h_{o1}
       -\frac{A-2C}{2Cd}j_{t0}-\frac C{2Ad}j_{o0}.
 \end{split}
 \tag{TB11}
\]

With \(\Delta=a-c\), define the gauges

\[
 \gamma_0=\frac{a h_{10}+2ac h_{11}-c h_{20}-2ac h_{21}}{\Delta},
 \qquad
 \gamma_1=\frac{-2h_{10}-c h_{11}+2h_{20}+a h_{21}}{\Delta}.
 \tag{TB12}
\]

Direct binary multiplication of the actual words gives

\[
 \kappa_{t1}|_0=\kappa_{t2}|_0=0,\qquad
 \gamma_0|_0=e_0,\qquad \gamma_1|_0=-r e_1.
 \tag{TB13}
\]

All six coefficient vectors lie in \(\ker U\). Their associated
source polynomial heads are, exactly,

\[
 p(\kappa_{t1})=\frac vA,\qquad
 p(\kappa_{t2})=-\frac vA,\qquad
 p(\gamma_0)=e_0,\qquad p(\gamma_1)=-r e_1.
 \tag{TB14}
\]

In particular, the \(\kappa\) combinations have exact completed row sum
zero for every \(\delta\), since \(K_t\mathbf1=\mathbf1\) and
\(v\mathbf1=0\). Their source rows need not have zero polynomial head.
The gauges' binary completed rows equal their polynomial heads, so
their actual source rows vanish at binary order.

The saved symbolic calculation checks every component of (TB13) and
(TB14), in addition to each \(\kappa\)'s row sum.

## Weak coefficients derived from the actual words

For the same ordered pair \((t,o)\), write \(A=a_t,C=a_o\). At binary
order the last kernel has zero output-2 column, and
\[
 [\delta](K_o)_{i2}=\frac{\beta rG_{i2}}{l_{oi}}.
 \tag{TB15}
\]
Therefore only the last-kernel derivative contributes to
\([\delta](K_tK_o)_2\). The derivative of an incoming external
coefficient \(\mu_{ti}\) also multiplies a zero binary output.
It follows directly from (TB3) that

\[
 \begin{split}
 w(h_{t0})&=
  \frac{\beta r(2l_{o1}-Arl_{o0})}{l_{t0}l_{o0}l_{o1}},\\
 w(h_{t1})&=
  \frac{-\beta r^2(l_{o1}-2Arl_{o0})}{l_{t1}l_{o0}l_{o1}},\\
 w(h_{t2})&=
  \frac{\beta r^2(l_{o1}-Arl_{o0})}{l_{t2}l_{o0}l_{o1}}.
 \end{split}
 \tag{TB16}
\]

With
\[
 \Omega_o=\frac{\beta r^2(1-3Cr)}{l_{o1}l_{o2}},
 \tag{TB17}
\]
the incoming coefficients are
\[
 w(j_{t0})=\frac{2\Omega_o}{l_{t0}},\qquad
 w(j_{t1})=\frac{-r\Omega_o}{l_{t1}},\qquad
 w(j_{t2})=\frac{r\Omega_o}{l_{t2}}.
 \tag{TB18}
\]

These are raw weak output coefficients, without division by \(r\).
All twelve formulas were independently obtained from the ordered
matrix products and cross-multiplied against (TB16)–(TB18).
Every weak coefficient is linear in \(\beta\).

## Actual ordinary residues and gauge elimination

Take weak residues of the four columns
\((\kappa_{11},\kappa_{12},\kappa_{21},\kappa_{22})\), denoted \(W\),
and the two columns \((\gamma_0,\gamma_1)\), denoted \(G_{\mathrm{res}}\).
Order the two pivot nodes and four remaining nodes as

\[
 \mathcal A=(2/a,2/c),\qquad
 \mathcal I=(1/(2a),1/a,1/(2c),1/c).
 \tag{TB19}
\]

Use ordinary \(r\)-residues throughout; a row-form residue must be
divided by the derivative of its row form. Formulas (TB11)–(TB18) give

\[
 G_{\mathcal A}=
 \begin{pmatrix}
 \dfrac{2\beta}{\Delta(a-4c)}
   &\dfrac{-4\beta}{a\Delta(a-4c)}\\[5pt]
 \dfrac{-2\beta}{\Delta(c-4a)}
   &\dfrac{4\beta}{c\Delta(c-4a)}
 \end{pmatrix},\qquad
 \det G_{\mathcal A}
   =\frac{8\beta^2}{ac\Delta(a-4c)(c-4a)}\ne0.
 \tag{TB20}
\]

Eliminate the gauges using these two actual residue rows:

\[
 Q=W_{\mathcal I}
       -G_{\mathcal I}G_{\mathcal A}^{-1}W_{\mathcal A}.
 \tag{TB21}
\]

Put \(U_*=a-2c,\ V_*=2a-c,\ T=U_*\Delta V_*\). All sixteen entries
of the resulting actual matrix satisfy the exact identities

\[
 Q=\frac{\beta}{8T}
       \operatorname{diag}(a^{-3},4a^{-3},c^{-3},4c^{-3})\,N,
 \tag{TB22}
\]

where

\[
 N=\begin{pmatrix}
 -2(a^2-3ac+11c^2)&6U_*^2&-9a(a+c)&6aV_*\\
 U_*(a-5c)&-6U_*\Delta&-a(a-5c)&0\\
 9c(a+c)&6cU_*&2(11a^2-3ac+c^2)&-6V_*^2\\
 -c(5a-c)&0&-V_*(5a-c)&6\Delta V_*
 \end{pmatrix}.
 \tag{TB23}
\]

The symbolic certificate derives \(W,G_{\mathrm{res}}\) from the
actual weak words, takes ordinary residues, and verifies (TB20) and
each entry of (TB22). It does not infer (TB22) merely from a determinant
comparison. At general \(\beta\), both \(W\) and \(G_{\mathrm{res}}\)
scale by \(\beta\), so (TB21) and (TB22) scale by \(\beta\) as well.

## An explicit two-by-two Schur proof

Apply the same permutation \((1,3,2,4)\) to the rows and columns of
\(N\). Write the reordered matrix as
\(\begin{pmatrix}A&B\\C&D_*\end{pmatrix}\). Its lower-right block is

\[
 D_*=\begin{pmatrix}-6U_*\Delta&0\\0&6\Delta V_*\end{pmatrix},
 \qquad
 BD_*^{-1}=\frac1\Delta
       \begin{pmatrix}-U_*&a\\-c&-V_*\end{pmatrix},
 \tag{TB24}
\]

and its lower-left block is

\[
 C=\begin{pmatrix}
 U_*(a-5c)&-a(a-5c)\\
 -c(5a-c)&-V_*(5a-c)
 \end{pmatrix}.
 \tag{TB25}
\]

Multiplication of these displayed two-by-two matrices gives

\[
 A-BD_*^{-1}C
       =\begin{pmatrix}-U_*\Delta&0\\0&\Delta V_*\end{pmatrix}.
 \tag{TB26}
\]

For example, the off-diagonal cancellation uses
\[
 U_*(a-5c)-V_*(5a-c)=-9\Delta(a+c);
 \tag{TB27}
\]
the two diagonal differences are respectively
\(-U_*\Delta\) and \(\Delta V_*\). Thus

\[
 \det N=36U_*^2\Delta^4V_*^2,\qquad
 \boxed{\det Q=
    \frac{9\beta^4}{64a^6c^6(a-2c)^2(2a-c)^2}\ne0.}
 \tag{TB28}
\]

Here \(a,c>0\), \(\Delta\ne0\), \(a-2c<0\), and \(2a-c>0\).
The factors \(a-4c\) and \(c-4a\) in (TB20) are also nonzero.
The same row and column permutation leaves \(\det N\) unchanged.

## Invertibility of the normalized two-block matrix

The weak residue matrix on the six coefficient vectors in (TB11)–(TB12),
with gauge columns placed first, has block form
\[
 \begin{pmatrix}
 G_{\mathcal A}&W_{\mathcal A}\\
 G_{\mathcal I}&W_{\mathcal I}
 \end{pmatrix}.
 \tag{TB29}
\]
Its determinant is \(\det G_{\mathcal A}\det Q\), which is nonzero by
(TB20) and (TB28). Hence the six formal coefficient vectors are
independent. They all belong to \(\ker U\), and (TB10) shows that they
form its basis.

If a coefficient vector has zero upper and weak observations in the
normalized limiting paired matrix, its upper observations first put it
in \(\ker U\). Matrix (TB29) then forces every coefficient in this
kernel basis to vanish. The full normalized \(12\times12\) paired
matrix is therefore invertible at \(h=\delta=0\).

This conclusion uses actual source residues. In particular, dividing a
polynomial head's output 2 by \(\delta\) still gives zero ordinary
residues for every nonzero \(\delta\), so the nonzero heads in (TB14)
cannot create a missing residue term. Analyticity at distinct binary
poles then preserves the nonzero determinant for sufficiently small
positive \(h,\delta\) in the original normalized family, with
\(\beta>0\). This provides the explicit two-block base. The
[nonzero-h transfer proof](SOURCE24_NONZERO_H_WEAK_TRANSFER.md)
separates the promoted weak functions. Its remaining constant-function
and polynomial-gauge residue directions still require a joint argument,
followed by the full-source correction.

## Verification scope

The external symbolic check used exact rational coefficients, factored
denominators, and sparse polynomial cross multiplication. Every accepted
factor cancellation was checked by multiplying back. All 85 identities
passed in one execution; the calculation took approximately 0.337 seconds,
and the full process took 0.43 seconds with peak RSS 16,908,288 bytes.
The certificate records its source hash, every zero polynomial identity,
and the denominator-factor registry.

The Schur proof (TB24)–(TB28) and the binary-surjectivity argument are
paper arguments displayed above; they are not represented as additional
Lean checks or as additional executions of the symbolic script.

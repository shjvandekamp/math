# The actual three-class coefficient under ordered confluence

Research note, 16 October 2026. This proves generic nonvanishing of
the actual coefficient \(\mathfrak J_m\) in (NH73) for every fixed
\(m\ge2\). It supplies an alternative completion of the paired
quotient route. The full equation-(24) retained-old determinant
remains open.

The argument uses the audited actual recurrence and endpoint results
in [SOURCE24_NONZERO_H_WEAK_TRANSFER.md](SOURCE24_NONZERO_H_WEAK_TRANSFER.md).
The confluence, endpoint sections, quotient algebra, and parity
coefficients were independently audited. A separate exact program
reconstructed the two-block boundary from its source words and passed
73 identities. The displayed algebraic supporting Lean lemmas do not
yet formalize this entire confluence or its source-space identification.

## Normalize the actual zero-endpoint space before taking a limit

Use the restricted actual image \(\mathcal A_m\) of (NH56), of
dimension \(2m-1\), and put
\[
 \mathcal R_m=\{c\in\mathcal A_m:c(0)=c(\infty)=0\},
 \qquad \dim\mathcal R_m=2m-3.
 \tag{CQ1}
\]
The actual recurrence, including its endpoint corrections, restricts to
\[
 \mathcal R_{m+1}
 =\mathcal N_{m+1}\oplus
   \chi_{m+1}\bigl(\mathcal R_m\cap\ker\operatorname{ev}_{1/A}\bigr).
 \tag{CQ2}
\]
The selected old functions have zero endpoints and zero new-node
evaluation, so every additional correction in the full transfer vanishes.

Fix \(\alpha=3/2\), set \(x=\alpha r,\ \theta=\alpha z\), and take
\(b_1=b_2=1,\ b_j=j-1\) for \(j\ge3\). Approach
\(a_1=\cdots=a_m=\alpha\) in the ordered hierarchy
\[
 a_j=\alpha-\sum_{\ell=j+1}^m\varepsilon_\ell,
 \qquad 0<\varepsilon_m\ll\cdots\ll\varepsilon_2.
 \tag{CQ3}
\]
Here the last gap tends to zero first. For every fixed length the
strictly ordered positive parameters can be kept in \((1,2)\).
Normalize \(c\) by \(P_m=D_m/(1-a_1r)\) before imposing the new-node
condition and taking the limit. Write
\[
 Q_\theta(x)=x^2+(2\theta-2)x-\theta,\qquad
 C_\theta(x)=(1+x)Q_\theta(x).
 \tag{CQ4}
\]
For \(\theta\) away from the displayed exceptional values, the flat limit is
\[
 \widehat{\mathcal R}_m^{\,\mathrm{col}}
 =C_\theta\,\operatorname{Laurent}[1-m,m-3],\qquad m\ge3.
 \tag{CQ5}
\]

Here is a direct check of both the normalization and flatness. In the
notation (NH64), (NH66), and (NH68), the three normalized new columns are
\[
 n_0=-\frac{2LF(1-2Ar)}{27Ar^2},\quad
 n_1=\frac{LF(2-Ar)}{27Ar},\quad
 n_*=-\frac{LJ}{9rN_\xi},\quad
 n_2=n_*-\frac z{Q_\xi}n_0-\frac2{Q_\xi}n_1.
 \tag{CQ6}
\]
Their Laurent coefficients are regular at the full diagonal because
\(Q_\xi^{-1}=3A(A-a_1)/N_\xi\). Their limits are
\[
 \frac{C_\theta}{x^2}
 \left(-\frac{2(1-2x)}{27\alpha},
       \frac{x(2-x)}{27\alpha^2},
       \frac{x}{9\alpha}\right).
 \tag{CQ7}
\]
The three quadratic coefficients have determinant
\(-2/(6561\alpha^4)\ne0\). Thus the new space loses no dimension.

The one-dimensional \(\mathcal R_2\) has zero evaluation kernel at an
independent generic new point, so \(\mathcal R_3=\mathcal N_3\).
Assume (CQ5) at length \(m\). Since
\(C_\theta(1)=2(\theta-1)\ne0\), the selected old space has limit
\[
 C_\theta(1-x)\operatorname{Laurent}[1-m,m-4].
 \tag{CQ8}
\]
The old normalized \(n_0\) is an explicit nonzero evaluation adjuster:
subtracting its suitable multiple constructs a basis regular in the
gaps. The actual selected transfer has limiting multiplier
\[
 -\frac{4b_{m+1}}{9\alpha}
 \frac{(x-\theta)(2-x)(1-2x)}{x(1-x)}.
 \tag{CQ9}
\]
After cancelling \(1-x\), the required direct sum is
\[
 \operatorname{Laurent}[-m,m-2]
 =x^{-2}\mathbb R[x]_{\le2}\ \oplus\
   \frac{(x-\theta)(2-x)(1-2x)}x
     \operatorname{Laurent}[1-m,m-4].
 \tag{CQ10}
\]
Evaluation at the three distinct nonzero points \(\theta,2,1/2\)
proves trivial intersection; the dimensions are \(3+(2m-4)=2m-1\).
This proves (CQ5) and flatness inductively. The first old state-2 pole
also coalesces, but no evaluation at that singular unnormalized limit
has been used: the condition is imposed on \(c/P_m\) first.

## The actual endpoint sections

At the first last-gap collision \(\varepsilon=A-a_{m-1}\to0\), the
actual endpoint multipliers satisfy
\[
 \kappa_0\sim\frac{za_{m-1}}{2\varepsilon},
 \qquad \kappa_\infty\sim-\frac1{2\varepsilon}.
 \tag{CQ11}
\]
Choose actual old endpoint sections, and subtract a multiple of an
actual zero-endpoint function to make their value at \(1/A\) vanish.
Normalize their full transfers by \(\kappa_0,\kappa_\infty\).
Their limits are \(-2W_0,-2a_{m-1}W_1\). For \(m\ge4\) the old
new-layer \(n_0\) supplies the required nonzero evaluation. For \(m=3\)
the exact two-block adjuster below supplies it.

After the remaining coalescence, write
\[
 d=-\frac{3x}{(2-x)(1-2x)},\quad
 q=-\frac{x}{2-x},\quad
 p=q\frac{1-d^m}{1-d},\quad P=\frac{d^m}{1-x}.
 \tag{CQ12}
\]
The resulting actual endpoint sections are
\[
 E_0=\frac23\left(1-\frac{x+1}{x}p\right),\qquad
 E_\infty=\frac23\left((x+1)(p+d^m)-x\right).
 \tag{CQ13}
\]
Their endpoint pairs are \((1,0),(0,1)\). Consequently the full actual
flat limit is
\[
 \mathcal A_m^{\mathrm{col}}
 =PC_\theta\operatorname{Laurent}[1-m,m-3]
     \oplus\operatorname{span}\{E_0,E_\infty\}.
 \tag{CQ14}
\]
This describes a limit of actual spaces, not the rank of the literally
coincident-parameter source matrix.

## Actual projection and the parity coefficients

Let \(J_\theta f=(f(x)-f(\theta))/(x-\theta)\), and define
\[
 U=J_\theta(p/x),\quad V=J_\theta p,\quad
 W=(1-2\theta)P-\frac{\theta}{2x}P+
                       3\theta(1-\theta)J_\theta P.
 \tag{CQ15}
\]
These are exactly the targets in (NH71)--(NH72), with
\(u=\alpha^2U,\ v=\alpha V,\ w=W\).
Their infinity values are zero; their values at zero are respectively
\[
 \frac{p(\theta)}{\theta^2}+\frac1{2\theta},\qquad
 \frac{p(\theta)}{\theta},\qquad 3(1-\theta)P(\theta).
 \tag{CQ16}
\]
For a target \(f\), subtract its actual endpoint sections and divide:
\[
 L_f=\frac{f-f(0)E_0-f(\infty)E_\infty}{P}.
 \tag{CQ17}
\]
Use quotient coordinates \((L_f(-1),A_f,B_f)\), where \(A_f+B_fx\)
interpolates \(L_f\) at the two roots of \(Q_\theta\).
Modulo (CQ5) these are three genuine actual quotient coordinates.
Their conversion matrix on the representatives \(P,Px,Px^2\) is
\[
 \begin{pmatrix}1&-1&1\\1&0&\theta\\0&1&2-2\theta\end{pmatrix},
 \qquad \det=3(1-\theta).
 \tag{CQ18}
\]

Put \(s=3^{-m},\ e=(-1)^m\). At \(\theta=-1\), direct rational
calculation gives the target-coordinate matrix
\[
 \begin{pmatrix}
 1-\frac1{3s}&0&-\frac92\\
 \frac{e+1}{6e}&0&0\\
 \frac{s-2es-1}{6e}&\frac{2es-e-s}{6e}&
                              \frac{4es+e-2s}{2e}
 \end{pmatrix}.
 \tag{CQ19}
\]
The first entry of the last row is the corrected entry. An earlier
exploratory response printed a different sign there; the corrected
matrix and the following formulas were independently checked.
Its determinant is
\[
 -\frac{(e+1)(2es-e-s)}{8e^2}.
 \tag{CQ20}
\]
For even \(m\), this is \((1-s)/4\). For odd \(m\), only the middle
row vanishes. Its derivative at \(\theta=-1\) is
\[
 \left(\frac{2(1-s)-m(1+s)}9,\
       \frac{(m+2)s-1}9,\
       \frac{2(m+2)s}3\right).
 \tag{CQ21}
\]
One way to check this derivative is reduction modulo \(Q_\theta\):
for odd \(m\),
\[
 p\bmod Q_\theta
 =\frac{2x-1}{3}+(\theta+1)\frac{(m+1)x}{3}
       +O((\theta+1)^2).
 \tag{CQ22}
\]
Replacing the zero row in (CQ19) by (CQ21) gives
\[
 \frac{(3s-1)((15m-9)s-2)}{108s}.
 \tag{CQ23}
\]
For every odd \(m\ge3\), \(3s<1\) and
\((15m-9)3^{-m}\le4/3<2\), so this coefficient is nonzero.
In canonical polynomial quotient coordinates, divide by (CQ18)
and include the factor \(\alpha^3\). For \(m\ge3\), this gives
\[
 \begin{cases}
 \mathfrak J_m^{\mathrm{col}}(-1)=\alpha^3(1-s)/24,
       &m\ \text{even},\\[2mm]
 [\eta]\mathfrak J_m^{\mathrm{col}}(-1+\eta)
   =\displaystyle\frac{\alpha^3(1-3s)(2-(15m-9)s)}{648s},
       &m\ \text{odd}.
 \end{cases}
 \tag{CQ24}
\]
The dependence of (CQ18) on \(\theta\) adds no term in the odd case,
because the original determinant vanishes there.
The numerical coefficients in (CQ24) refer to this canonical frame.
For a different quotient map in (NH73), an invertible rational change
of coordinates preserves nonidentity, but need not preserve these
particular boundary coefficients.

These nonzero rational coefficients prove generic nonidentity for
every fixed length. Negative \(z\) was used only to certify a rational
nonidentity. Intersecting the finitely many denominator and rank opens
with the positive parameter region returns admissible generic choices.
No single numerical point is asserted to work for all lengths.

## Exact two-block boundary and reproduction

At \(a_1=1,a_2=3/2,b_1=b_2=1,z=-2/3\), use source order
\((H_1,J_1,H_2,J_2)\), three states in each group. The three coefficient
vectors are
\[
 \begin{aligned}
 \gamma_1&=(-14,-114,-33,36,27,-27,36,81,0,0,0,0),\\
 \gamma_2&=(-20,-24,-24,0,0,0,36,0,0,27,0,0),\\
 \gamma_3&=(20,24,24,-36,-27,27,-36,0,0,0,81,0).
 \end{aligned}
 \tag{CQ25}
\]
The exact checker derives their binary annihilation and retained heads
\((-33,-24,24)v\) from the actual H/J formulas. The complete binary
constraint matrix has rank eight. On its four-dimensional kernel,
the removed-pole functional is \((0,0,0,4/9)\) in the reconstructed
basis. The three displayed independent weak images therefore form
the actual restricted \(\mathcal A_2\).

Put \(D=(r-2)(r-1)(2r-1)(3r-4)(3r-1)\). Multiplying
\((c_1,c_2/4,c_3,(8/3)u,4v,(14/9)w)\) by \(D\) gives the
ascending coefficient matrix
\[
 \begin{pmatrix}
 -144&-54&144&4&20&-4\\
 1108&244&-472&-53&-139&21\\
 -2159&-143&446&146&298&-16\\
 -699&-375&798&-127&-221&-35\\
 1980&198&-711&30&42&6\\
 -486&0&0&0&0&0
 \end{pmatrix}.
 \tag{CQ26}
\]
Its exact determinant is \(-2^6 3^{12}20161\ne0\), proving
\(\mathfrak J_2\ne0\). The remaining endpoint adjuster is
\[
 c_*=2c_2+3c_3
 =-\frac{r(549r^3+606r^2-194r-536)}D,\quad
 c_*(0)=c_*(\infty)=0,\quad c_*(2/3)=-525.
 \tag{CQ27}
\]
This supplies the missing length-three endpoint-section condition.

Reproduce the external finite certificate with:

    python3 exploration/source24_confluent_quotient_base.py \
      --output certificates/source24_confluent_quotient_base.json

The recorded run passed 73 exact rational identities in 0.077 seconds
with 15.8 MB peak RSS. Its elimination operations are replayed exactly;
no floating-point rank inference is used.

The supporting module SourceConfluentQuotientAlgebra.lean proves the
displayed matrices' determinant formulas and the required inequalities
for every natural length at least three. It does not identify the
replacement row as the actual analytic derivative or formalize the
source-space confluence.

Combined with the already audited (NH74), the result proves a nonzero
coefficient of that actual paired quotient pencil for every length.
It does not prove the different retained-old-source Schur determinant
\(H_q\), nor an end-to-end Lean equation-(24) theorem.

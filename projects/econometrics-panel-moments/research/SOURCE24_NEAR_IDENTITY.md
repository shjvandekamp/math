# Leading blocks near an identity transition matrix

**Status: independently audited bounded paper calculation; no independence theorem.** This note
records two obstructions to a simple leading-block argument. It makes no
claim that the full degeneration fails: higher coefficients and couplings
between the blocks remain available. No numerical calculation or Lean
formalization is used here.

Take
\[
 G_\varepsilon=I+\varepsilon C,\qquad
 A_t=G_\varepsilon\operatorname{diag}(B_{t0},B_{t1},B_{t2}),
 \quad B_t=(1,u_t,v_t),
\]
with positive off-diagonal entries of \(C\) and nonzero time factors.
Row scaling makes the first column of the common matrix one when
\(\varepsilon\ne0\), without changing any transition kernel. For
transparent orders, work before that scaling and use the line forms
\[
 \ell_{ta}=L_{ta}/B_{ta},\qquad
 v_{ta}=(G_{\varepsilon,ab}(B_{tb}/B_{ta})X_b)_b.
\]
Thus \(K_t(a,:)=v_{ta}/\ell_{ta}\). All these changes are
nonzero parameter or Laurent scalings of the original residue coordinates.

The source row under consideration is the actual ordered-product row
\[
 F_{t,s,a,b}=X_aK_t(a,b)e_b(I-P_s^{\widehat t}),
 \tag{N1}
\]
where \(P_s^{\widehat t}\) puts \(s\) first and then the
other blocks besides \(t\) in increasing order. All spans below use
constant coefficients in the effect variables.

At a pair of pole lines use the double residue
\((\ell_{uc}\ell_{vd}F)(P)\), expressed in the two zero-sum
vectors \(v_{uc}(P),v_{vd}(P)\). The following assertions concern
the indicated limiting submatrices in these explicit coordinates.
Assume the displayed limiting intersections and residue bases are generic:
the nonmarked denominators used in each calculation do not vanish there,
and the two residue vectors remain independent after their stated scaling.

## Same-state line pairs

Fix a state \(c\), and denote the other states by \(b,e\). Use
the blow-up \(X_c=\varepsilon x\), leaving \(X_b,X_e\) as
the other homogeneous coordinates. Then
\[
 \ell_{tc}=\varepsilon\lambda_t+O(\varepsilon^2),\qquad
 \lambda_t=x+C_{cb}\frac{B_{tb}}{B_{tc}}X_b
                 +C_{ce}\frac{B_{te}}{B_{tc}}X_e.
 \tag{N2}
\]
The limiting kernel fixes states \(b,e\). Its state-\(c\) row is
\[
 K_t^0(c,:)=\frac1{\lambda_t}
 \left(x,\ C_{cb}\frac{B_{tb}}{B_{tc}}X_b,
             C_{ce}\frac{B_{te}}{B_{tc}}X_e\right),
 \tag{N3}
\]
written in the order \((c,b,e)\). Thus state \(c\) is transient
and the other two states are absorbing. The probability of staying in
state \(c\) is \(p_t=x/\lambda_t\); a product's state-\(c\)
survival entry is the product of these scalars, regardless of its order.

For every diagonal shared-source column \((t,s,c,c)\), the rational
row \(\varepsilon^{-1}F_{t,s,c,c}\) has a finite limit. Its
state-\(c\) component is exactly
\[
 \frac{x^2}{\lambda_t}
       \left(1-\prod_{j\ne t}\frac{x}{\lambda_j}\right)
 =\frac{x^2}{\lambda_t}
       -\frac{x^{m+1}}{\prod_j\lambda_j}.
 \tag{N4}
\]
The first term has only one pole. Therefore its state-\(c\) double
residues are independent of both \(t\) and \(s\).

There are \(\binom m2\) pairs of state-\(c\) lines and two
zero-sum residue coordinates per pair. Projection to the state-\(c\)
component has a kernel of dimension one at each pair. Equation (N4)
shows that the image of all the columns under this projection has rank
at most one. Consequently the square same-state/diagonal-source leading
block has
\[
 \operatorname{rank}\le 1+\binom m2,
 \qquad\text{number of columns}=m(m-1).
 \tag{N5}
\]
This upper bound is strictly smaller than the column count for every
\(m\ge3\).

For the translation to residue orders, each marked line and residue
vector is of order \(\varepsilon\). The unnormalized double
residue of (N1) is therefore of order \(\varepsilon^3\), and
its two coordinates in the residue-vector basis are of order
\(\varepsilon^2\). Their coefficient after division by
\(\varepsilon^2\) is precisely the leading block in (N5).
This statement concerns diagonal source labels with the same marked
state; it is not a rank bound for the full source matrix.

## Distinct-state line pairs

Fix two distinct states \(c,d\), and let \(e\) be the remaining
state. Near their limiting coordinate vertex take
\(X_c=\varepsilon x\), \(X_d=\varepsilon y\), \(X_e=1\).
Put
\[
 a_t=C_{ce}\frac{B_{te}}{B_{tc}},\qquad
 b_t=C_{de}\frac{B_{te}}{B_{td}},\qquad
 p_t=\frac{x}{x+a_t},\quad q_t=\frac{y}{y+b_t}.
\]
The limiting kernels, in state order \((c,d,e)\), are
\[
 K_t^0=\begin{pmatrix}
 p_t&0&1-p_t\\
 0&q_t&1-q_t\\
 0&0&1
 \end{pmatrix}. \tag{N6}
\]
They commute. Each of the two transient states can escape only to the
remaining absorbing state.

For the off-diagonal source label \(c\to d\),
\[
 \varepsilon^{-2}F_{t,s,c,d}\longrightarrow
 C_{cd}\frac{B_{td}}{B_{tc}}\frac{xy}{x+a_t}
 e_d\left(I-\prod_{j\ne t}K_j^0\right).
 \tag{N7}
\]
This entire limiting rational row is independent of the first slot
\(s\). Its mixed poles involve the shared line \((t,c)\) and
a state-\(d\) line. The reverse source label has the analogous
formula with \(c,d\) exchanged.

Other off-diagonal source labels do not contribute a mixed state-\(c\),
state-\(d\) double residue at this order. A source entering \(c\)
or \(d\) from \(e\) has a leading row depending on only one
of \(x,y\). A source entering \(e\) starts in an absorbing
state, so its relevant mixed contribution occurs at a higher order.

Thus, across all distinct-state rows, the leading off-diagonal columns
with the same \((t,a,b)\), \(a\ne b\), are identical as
\(s\) varies. There are only \(6m\) such groups. The resulting
leading submatrix satisfies
\[
 \operatorname{rank}\le6m,
 \qquad\text{number of columns}=6m(m-1).
 \tag{N8}
\]
It is deficient for every \(m\ge3\). Here the two marked lines
and their residue vectors again have order \(\varepsilon\).
Equation (N7) gives raw double residues of order
\(\varepsilon^4\), or residue-vector coordinates of order
\(\varepsilon^3\). The leading matrix in (N8) uses the latter
coordinates divided by \(\varepsilon^3\).

## Scope of the obstruction

The natural same-state diagonal block and the distinct-state
off-diagonal block both lose first-slot information at leading order.
They therefore do not supply invertible diagonal blocks for a direct
leading triangular determinant argument. The counts (N5) and (N8) are
individual subblock bounds, not an asserted full-matrix rank formula.
Higher coefficients can distinguish the first slot, and off-diagonal
couplings can interact with the missing same-state directions. None of
those higher-order or mixed arguments has been ruled out or completed.

An independent Astra reviewer checked the two limiting kernels, component
and support arguments, residue-coordinate orders, and rank bounds. The
primary researcher reviewed the stated scope before integration.

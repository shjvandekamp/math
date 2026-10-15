# A uniform even-length conic transverse correction

**Status: independently audited paper proof, conditional on the established
binary parity and outer-support theorems; not Lean formalized.** This proves
generic nonvanishing of the outgoing transverse block for every even old
length. Together with the odd leading block, it covers every old length.
It does not prove nonvanishing of the regular/longitudinal Schur block
(CT8), or independence of the complete source family.

The binary inputs are (L2)--(L4) in
[SOURCE24_INDUCTION.md](SOURCE24_INDUCTION.md#a-last-block-degeneration-and-its-binary-obstruction),
including constant-real-linear independence and the scalar parity recurrence.
The normalized ordered-word rank theorem is formalized in
[BinaryTransferRank.lean](../formal/PanelMoments/BinaryTransferRank.lean);
the matrix-product interpretation and this perturbation argument remain paper
results. The transverse coordinates and actual source normalization are
(CT1)--(CT5) in [SOURCE24_CONIC_TRANSVERSE.md](SOURCE24_CONIC_TRANSVERSE.md).
This is a local derivation, not a result attributed to the still-pending
external Pro12 investigation.

## Binary deformation and exact identities

Fix an even length \(n=2\ell\ge2\), \(\rho\ne0,1\), nonzero \(c_i\), and
distinct consecutive \(c_i\). Write \(h=\rho-1\). Introduce a scalar
deformation \(\delta\) of the binary odds:
\[
 a_i=c_i,\qquad b_i=\rho c_i+\delta,\qquad
 \omega_i=b_i-a_i=hc_i+\delta.
 \tag{J1}
\]
All following expressions are considered near \(\delta=0\), where their
displayed denominators are nonzero. The binary transition has rows with
outcome-two odds \(a_i z,b_i z\). Its inverse determinant and normalized
off-diagonal entries are
\[
 H_i=\frac{(1+c_i z)(1+b_i z)}{\omega_i z},\quad
 Q_i=\frac{c_i(1+b_i z)}{\omega_i},\quad
 R_i=\frac{1+c_i z}{\omega_i},\quad
 H_i=1+Q_i+R_i/z.
 \tag{J2}
\]
Let
\[
 A_k=\prod_{i=1}^kH_i,\quad
 U_k=\sum_{i=1}^k A_{i-1}Q_i,\quad
 V_k=\sum_{i=1}^k A_{i-1}R_i,
 \qquad A_0=1,\quad U_0=V_0=0.
 \tag{J3}
\]
Thus \(A_k=1+U_k+V_k/z\). These are the actual ascending normalized
word sums. Define \(h_1=0\) and, for \(s\ge2\),
\[
 h_s=\frac{R_sU_{s-1}-Q_sV_{s-1}}z.
 \tag{J4}
\]
Moving block \(s\) first, while keeping the other blocks in increasing
order, changes the normalized \(Q\) word by \(h_s\) and the normalized
\(R\) word by \(-zh_s\). These are constant column differences.
For a variable appended parameter \(c\), the notation
\(h_{k+1}(c)=(R_cU_k-Q_cV_k)/z\) uses the same one-block formulas.

Put
\[
 \Psi_k(c)=-\frac{1+\rho cz}{z}V_k.
\]
Here \(\Psi_0=0\). For \(k\ge1\), \(e=c_k\ne c\), direct substitution
gives the exact recurrence
\[
 \Psi_k(c)=1-\Psi_{k-1}(e)+\delta V_{k-1}
       +\frac{\omega_eh_k-\omega_ch_{k+1}(c)}{e-c}.
 \tag{J5}
\]
One verification first uses
\(\Phi_k(c)=-(1+b_cz)V_k/z=\Psi_k(c)-\delta V_k\).
Expansion of \(U_k=U_{k-1}+A_{k-1}Q_e\) and
\(V_k=V_{k-1}+A_{k-1}R_e\) yields
\[
 \Phi_k(c)=1-\Phi_{k-1}(e)
  +\frac{\omega_eh_k-\omega_ch_{k+1}(c)}{e-c}-\delta V_k,
 \]
which is (J5). Iterating (J5) for even \(k\) shows, modulo the
constant scalar span of \(h_2,\ldots,h_k,h_{k+1}(c)\),
\[
 \Psi_k(c)\equiv
 \delta\sum_{\substack{i<k\\i\ {\rm odd}}} A_{i-1}R_i.
 \tag{J6}
\]
This congruence is exact in \(\delta\).

## Outer elimination retains the correction

Write \(c=c_{n-1}\), \(d=c_n\), and \(U=U_{n-2}\),
\(V=V_{n-2}\), \(A=A_{n-2}\). For the two-block word \(cd\), use
\(Q_{cd}=Q_c+H_cQ_d\), \(R_{cd}=R_c+H_cR_d\), and
\(h_{cd}=(R_dQ_c-Q_dR_c)/z\). Set
\[
 v_Q=\frac{d+(b_cb_d/\rho)z}{c-d},\qquad
 v_R=\frac{1+(b_c/\rho)z}{c-d},\qquad
 S=\frac{v_QV-v_RU}{z}.
 \]
The multipliers \(v_Q,v_R\) are linear in \(z\), so their use
removes constant combinations of \(h_n,zh_n\). Exact identities are
\[
 R_dv_Q-Q_dv_R
   =z\left(1+\frac{\delta}{\rho(c-d)}\right),
 \qquad
 S=\Psi_{n-2}(c)-\frac{\omega_c}{c-d}h_{n-1}
      +\frac{\delta(b_dV-U)}{\rho(c-d)}.
 \tag{J7}
\]
In particular, the extra term in the first identity is retained.
Let \(q_{\rm res}=Q_{cd}-v_Qh_{cd}\) and
\(r_{\rm res}=R_{cd}-v_Rh_{cd}\). Their explicit values are
\[
 q_{\rm res}
 =\frac{-\delta^2/\rho
   -z\{\delta h\,c\,d+\delta^2(c+d)+\delta^3/\rho\}}{\omega_c\omega_d},
 \quad
 r_{\rm res}=\frac{\delta(h-\delta z)}{\rho\omega_c\omega_d}.
 \tag{J8}
\]
The two retained bracket corrections simplify exactly:
\[
 q_{\rm res}+\frac{\delta b_dz h_{cd}}{\rho(c-d)}
       =\delta R_cQ_d,\qquad
 r_{\rm res}+\frac{\delta z h_{cd}}{\rho(c-d)}
       =\delta R_cR_d.
 \tag{J9}
\]
Indeed, substitute
\(h_n=(R_dU-Q_dV)/z+A h_{cd}\) into (J7), and use
\(1+Q_d=b_dR_d\). Equations (J6)--(J9) give
\[
 U_n\equiv\delta Q_nT(\delta),\qquad
 V_n\equiv\delta R_nT(\delta),\qquad
 T(\delta)=\sum_{\substack{i<n\\i\ {\rm odd}}}A_{i-1}R_i
 \pmod{\operatorname{span}_{\mathbb R}\{h_s,zh_s:2\le s\le n\}}.
 \tag{J10}
\]
The span and its coefficients vary analytically with the parameters.
Every discarded scalar-\(h\) term is multiplied only by a linear
\(Q_n\) or \(R_n\), hence remains a constant combination of the paired
columns. No vector-space quotient has been treated as a ring.

## The two-dimensional first correction

Now evaluate all objects at \(\delta=0\). The established outer-support
theorem gives
\[
 {\cal V}_n=\operatorname{span}_{\mathbb R}\{z^{1-n},\ldots,z^n\}
       =I_n\oplus\operatorname{span}_{\mathbb R}\{1,z\},
 \quad I_n=\operatorname{span}_{\mathbb R}\{h_s,zh_s:2\le s\le n\}.
 \]
Let \(\Pi_n\) be this constant-linear projection. Its restriction to
\({\cal V}_j\), \(j<n\), equals \(\Pi_j\): the unique outer powers
force all later paired coefficients to vanish.

The baseline pair \(U_n,V_n\) lies in \(I_n\) for even \(n\).
Subtracting its constant leading expansions in the paired columns gives
two kernel columns. Differentiating the exact congruences (J10)
shows that their induced first derivatives are
\[
 \Pi_n(Q_nT),\qquad \Pi_n(R_nT).
 \tag{J11}
\]
Analytic changes in the eliminated coefficients contribute only the
leading image; they do not change (J11).

Write
\[
 A_{\rm o}=\sum_{i\ {\rm odd}}\frac1{c_i},\qquad
 A_{\rm e}=\sum_{i\ {\rm even}}\frac1{c_i},\qquad
 C=\sum_{j=1}^{\ell}\frac1{c_{2j-1}c_{2j}}.
 \]
Since \(T=\sum_{i\ {\rm odd}}(V_i-V_{i-1})\), parity gives
\[
 \Pi_nT=\frac{A_{\rm o}+\ell z}{h}.
 \]
For \(0\le i<n\), multiplying the scalar parity relation
\(\Psi_i(c_{i+1})\equiv i\bmod2\) by \(z\) uses only available
paired columns. Consequently
\[
 \Pi_n(zV_i)=
 \begin{cases}0,&i\text{ even},\\
 -(z+R_i)/(\rho c_{i+1}),&i\text{ odd},
 \end{cases}
 \qquad
 \Pi_n(zT)=-\frac{C+\rho A_{\rm e}z}{\rho h}.
 \tag{J12}
\]
Finally \(Q_n=\rho c_nR_n-1\) and \(R_n=(1+c_nz)/(hc_n)\).
The determinant of (J11), in the basis \(1,z\), is therefore
\[
 \boxed{\quad
 \det\bigl(\Pi_n(Q_nT),\Pi_n(R_nT)\bigr)
   =\frac{\rho A_{\rm o}A_{\rm e}-\ell C}{\rho(\rho-1)^3}.
 \quad} \tag{J13}
\]
This is a determinant on the actual leading kernel, not the rank of
stacked jets. For positive \(c_i\), \(A_{\rm o}A_{\rm e}\ge C>0\).
Thus \(\rho=\ell+1\) makes (J13) strictly positive.

## Actual conic normalization and the finite-parameter bridge

Use conic tables \(A_t(a,b)=(\alpha_a b_t)^b\), with
\[
 c_t=\alpha_1b_t,\qquad
 \rho=\alpha_2/\alpha_1,\qquad \eta=\alpha_0/\alpha_1.
 \]
On the appended line use \(X(x,y)=(xy,-x-y,1)\), where
\(x=\alpha_c\epsilon\) in sector \(c\), and \(h_x=(x,0,-y)^T\).
The two normalized binary transverse scalar columns from (CT2) are
\[
 \phi_{s1}=-(x+y)e_1P_s(x,y)h_x,\qquad
 \phi_{s2}=e_2P_s(x,y)h_x.
 \tag{J14}
\]
In the standard chart \((\xi,1,z)\), put
\(A_s=(P_s)_{12}\), \(B_s=z(1-(P_s)_{22})\).
At \(x=0\), \(z=-1/y\), and
\(\phi_{s1}=y^2A_s,\ \phi_{s2}=-y-y^2B_s\).
For any constant leading binary kernel relation
\(\sum_s(p_sA_s+q_sB_s)=0\), form the actual CT combination
\(G=\sum_s(p_s\phi_{s1}-q_s\phi_{s2})\).
Its leading term is the pole-free polynomial \(y\sum_s q_s\).
The moving standard coordinates are
\[
 \xi=-xy/(x+y)=-x+O(x^2),\qquad
 \zeta=-1/(x+y)=z+x/y^2+O(x^2).
 \]
Differentiating the kernel identity in \(z\) cancels the changing
prefactors and the common \(\zeta\) tangent, giving exactly
\[
 \partial_xG(0,y)
   =-y^2\sum_s\bigl(p_s\partial_\xi A_s+
                         q_s\partial_\xi B_s\bigr)_{(0,-1/y)}.
 \tag{J15}
\]
Thus the actual CT first correction is the fixed-\(z\) leakage
correction, with a common nonzero rational function factor. Division by
the common determinant product is a function-space isomorphism here;
it is not merely a rescaling of individual residues.

Take the boundary \(\eta=1\). States zero and one then have identical
transition rows and can be grouped. Their exact binary odds in
\((\xi,1,z)\) are
\[
 a_i(\xi)=\frac{c_i^2}{c_i+\xi},\qquad
 b_i(\xi)=\frac{\rho^2c_i^2}{\rho c_i+\xi}.
 \tag{J16}
\]
Both derivatives at zero equal \(-1\). The common-\(\rho\) tangent
obtained by changing \(c_i\) contributes only the leading image:
differentiate an analytic leading kernel basis along that
constant-rank family. The remaining tangent is exactly
\(b_i-\rho a_i=h\xi+O(\xi^2)\). Therefore the determinant of the
binary induced \(\xi\) correction is \(h^2\) times (J13), in the
baseline kernel basis.

The state-zero pivots must be retained in this boundary argument.
Before the boundary, their leading functions satisfy
\[
 \frac{(P_s)_{02}}D=\frac{(P_s)_{12}}D+Z_s,\qquad
 Z_s=\frac{\eta-1}{h}\frac{1+\rho c_sz}{1+\eta c_sz},
 \tag{J17}
\]
where \(D=\prod_i\det B_i\). This follows directly by propagating
the first-block row-zero/row-one difference through the suffix
determinants. For even length the normalized binary part belongs to
\(I_n\), so it can be removed by constant binary column operations.
Divide the remaining state-zero pivot by \(\eta-1\). Its limit is
\[
 D\,\frac{1+\rho c_sz}{h(1+c_sz)}.
 \tag{J18}
\]
Assume the binary nodes are distinct. Each function (J18) has a
unique nonzero double pole at \(z=-1/c_s\). Leading binary functions
have only simple poles. Their kernel derivatives also have only simple
poles: a moving-pole double coefficient is its common pole velocity
times the zero total residue of the leading kernel relation.
Consequently the normalized state-zero pivots cannot absorb any
nonzero binary first correction.

For precision about residues, work before division by \(D\) in the
class of rational functions regular at zero, zero there, and bounded
at infinity. Leading binary columns, their kernel derivatives, and
(J18) all belong to this class. All principal parts determine such a
function; when all poles are simple, ordinary finite residues suffice.
The limiting double poles are confluent observations, not an assertion
that ordinary residues alone detect double-pole functions.
Multiplication by \(y^2\) and \(z=-1/y\) preserves residue injectivity
at the nonzero old nodes.
Indeed, zero residues in the finite simple-pole geometry make
\(y^2H(-1/y)\) a polynomial of degree at most one; boundedness of
\(H\) at infinity forces that polynomial to vanish to order at least
two at zero, hence to be zero.

There are now \(n\) independent limiting state-zero pivots,
\(2n-2\) binary leading pivots, and two independent first kernel
derivatives. Fixed ordinary evaluations witness a nonzero minor of
these \(3n\) functions. This minor persists for finite \(\eta\)
sufficiently close to one. Only the normalized leading pivot columns
and the binary kernel derivatives require finite limits; no assertion
is made that every normalized pivot derivative has a finite limit.
For finite \(\eta\ne1\), restore disjoint simple-pole geometry.
The same function-class argument then gives the actual transverse
residue rank, and first-kernel elimination supplies a nonzero
\(x^2\) coefficient of the normalized transverse determinant (CT3).

For an explicit positive parameter choice, take
\[
 \rho=\ell+1,\qquad c_i=(\rho+1)^{i-1},\qquad
 \alpha=(\eta,1,\rho),\qquad b_i=c_i.
 \tag{J19}
\]
Binary node collisions are excluded because \(\rho\) is not an
integer power of \(\rho+1\). Choose finite \(\eta\) near one, unequal
to one and avoiding the finitely many forbidden node ratios.
The common conic transition matrix is then positive and invertible.
Small positive appended \(\epsilon\) gives the actual table with time
factors \((1,\epsilon,\epsilon^2)\). Each new-state sector uses the
same calculation with \(x=\alpha_c\epsilon\), so all three are
nonzero simultaneously. These parameters already have scalar
covariate slopes \((0,1,2)\); no independent-time substitution is needed.

Hence the conic outgoing transverse determinant is generically
nonzero for every even \(n\). The established odd binary leading rank
supplies the odd case. The longitudinal/regular correction (CT8)
remains a separate unresolved determinant.

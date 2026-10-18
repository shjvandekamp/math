# Terminal peeling and completion annihilator recursion

**Status: independently audited conditional construction; no incoming-rank theorem.**
Source: the user-authorized [GPT-6 Pro discussion](https://chatgpt.com/c/6ad12774-df98-83eb-96c6-246b17d5810e).
The primary researcher and an independent Astra reviewer checked the
construction below. Selected identities also have exact finite checks.
Notation is that of SOURCE24_COMPLETION_QUOTIENT.md. Inherit its full
geometry: every old-line intersection, including same-block intersections,
has nonzero coordinates, there are no triple intersections, and the
coordinate-edge residue evaluations have their stated nonzero denominators.
Assume invertible G and invertibility of the final old pair-source matrix O_m. The construction
does not assume incoming complementarity at shorter lengths.

## Raw rows and exact append

Put d(eta)=eta diag(X), and enlarge W_m by the three coordinate-vertex rows:

\[
 \widehat W_m=W_m\oplus d(K^3),\quad \dim\widehat W_m=9m^2+3.
 \tag{T1}
\]

For R in this space, nu(R)_a=R_a(e_a), and N(R)=R−d(nu(R)) projects to W_m.
Define the raw completed rows

\[
 \widehat Q_{t,s,a,b}=Q_{t,s,a,b}+\delta_{ab}X_ae_a
                  =X_aK_t(a,b)e_bP_s^{B\setminus\{t\}}. \tag{T2}
\]

For q=m−1, let S_m(R)=R K_m. This is injective and preserves the enlarged
ambient conditions. In divided-coordinate form it is right multiplication
by tilde K_m, whose new-line residue contains the matching X_a factor.
Old cross residues stay zero-sum under multiplication by K_m; new cross
residues are multiples of the new zero-sum residue vector. For t,s<=q,

\[
 \widehat Q^{(m)}_{t,s,a,b}=S_m\widehat Q^{(q)}_{t,s,a,b}. \tag{T3}
\]

For normalized rows the extra term is essential:
Q_m=Q_q K_m+delta_ab Xa ea(K_m−I). Final invertibility of O_m implies
independence of every prefix raw family: append any putative prefix relation
to get a relation among a subset of the final raw family, whose pair matrix
is −O_m. This does not assert invertibility of every O_q.

## Three cubic divisions

Let Phi_m(R)=D_all,m R diag(X)^-1, C_m=D_m tilde K_m, B_m=A_m^-1, and

\[
 h_{m,a}=X_a\prod_{c\ne a}L_{mc},\qquad
 C_m B_m=\operatorname{diag}(h_{m,a}). \tag{T4}
\]

Since Phi_m(S_m R)=Phi_q(R) C_m, each component of its right product by
B_m is h_m,a times the corresponding old polynomial component. For any
R in widehat W_m, use single-divisor polynomial division with a fixed
monomial order (a linear quotient/remainder rule) to write

\[
 (\Phi_m(R)B_m)_a=h_{m,a}b_a+r_a. \tag{T5}
\]

The quotient b is homogeneous of degree 3q. Besides zero remainders, it
must satisfy the old ambient conditions. These can be tested by an explicit
projection Pi_q onto A_q=Phi_q(widehat W_q), independently of the sources.

For an arbitrary degree-3q row b, form R_b=b diag(X)/D_all,q. At each
cross-block intersection, project its double residue r to the zero-sum
plane by r−(sum r)e0 and express it in the ordinary pair basis; call this
rho-circle. Define T-circle by the usual normalized line residue for c!=0.
For c=0 use the finite part: on L_i choose x=X0/X2 and
g_i,d(x)=Res_Li(R_b,d/Xd)/X2, and set T-circle_i,d=g'_i,d(0)/A_i,d.
For an actual ambient row the matching zero makes this precisely T.
Finally eta_a=R_b,a(e_a). Set

\[
 \Pi_q b=\Phi_q(\mathcal U_q\rho^\circ R_b
                          +V_qT^\circ R_b+d(\eta)). \tag{T6}
\]

This fixes every row of A_q by C4 and vertex normalization, so it is a
projection. For q=0 use the identity on constant rows. Define

\[
 P_m(R)=\Phi_q^{-1}(\Pi_q b),\qquad
 E_m(R)=(r,b-\Pi_qb). \tag{T7}
\]

Then P_m S_m=Id and ker E_m=S_m(widehat W_q): zero defect is exactly
divisibility with an old ambient quotient, and T4 identifies the appended
row. Thus rank E_m=18m−9. Compress its coefficient observations by choosing
the first independent rows on the known basis {U_m e_i,V_m e_j,d(e_a)}.
Call the resulting (18m−9)-row map epsilon_m. This compression is geometric;
it is not a source inverse and no computational cost bound is asserted.

## Recursive annihilator

Construct ellhat_m:widehat W_m→K^(9m+3), with kernel the raw completion span
Qhat_m. Start at m=0 with ellhat_0(d eta)=eta. Given ellhat_q, put

\[
 \Gamma_m(R)=\binom{\epsilon_m(R)}{\widehat\ell_q(P_mR)}. \tag{T8}
\]

This has 27m−15 rows and kernel S_m(Qhat_q), hence full row rank. The
remaining raw completion columns are exactly the 18(m−1) boundary columns
with t=m or s=m. Let C_partial=Gamma_m Qhat_partial. They have full column
rank, since a relation modulo the interior family would contradict raw
independence inherited from final O_m.

Choose a nonzero maximal row minor I, leaving rows J, and put

\[
 \mathfrak A_m=E_J-(C_{\partial})_J(C_{\partial})_I^{-1}E_I,
 \qquad \widehat\ell_m=\mathfrak A_m\Gamma_m. \tag{T9}
\]

Then ker ellhat_m=Qhat_m, and its rank is 9m+3. The inverse can be replaced
by determinant times identity and an adjugate. The source-dependent solve
at stage m is an 18(m−1)-square boundary minor, with parameter dependence
retained; it is not the 9m(m−1)-square O_m inverse.
For m=1 the boundary family is empty: use the empty minor with determinant
one, and let the boundary elimination be the identity.

At the final length ellhat_m d has rank three: any raw completion
combination which is a diagonal row has zero pair data, and O_m is invertible.
An explicit row annihilator of these three columns gives
ell_m:W_m→K^(9m), with ker ell_m=Q_m. Indeed, ell_m R=0 means
R−d eta lies in Qhat_m; vertex normalization puts R in Q_m.

## Remaining boundary matrix

The square matrix

\[
 \mathfrak B_m=[\Gamma_m\widehat Q_{\partial m}\mid
                 \Gamma_m d\mid\Gamma_m\mathcal U_m Z_m]
 \tag{T10}
\]

has size 27m−15. Its determinant is nonzero exactly when
W_m=Q_m direct-sum U_m(im Z_m). The first 18(m−1)+3 columns are already
independent under O_m invertible; the unresolved assertion concerns the
last 9m columns. This is an explicitly constructed border criterion, not
a proof of its nonvanishing and not a claim that its size is smaller than
the formal 9m quotient determinant.

## A transport commutator that cannot be omitted

For marked completed seeds R_tA from C6, write d_tA=delta_A0−c_tA and
Rhat_tA=R_tA−d_tA X0e0. For q>=2 and t<=q, appending a last block leaves
c_tA unchanged and gives

\[
 R^{(m)}_{tA}=R^{(q)}_{tA}K_m+d_{tA}X_0e_0(I-K_m). \tag{T11}
\]

At an old pair point P, let r=rho_P(R_tA^q), and put E=e2 w, so rE=r2 w.
The correction in T11 has no old double residue. The discrepancy between
coordinate transfer after append and append after coordinate transfer is

\[
 \rho_P(\mathcal A_B^{(m)}R_{tA}^{(m)}
             -S_m\mathcal A_B^{(q)}R_{tA}^{(q)})
     ={P_B\over P_2}\,r[K_m(P),E]. \tag{T12}
\]

This is a discrepancy at old nodes, not only at the new boundary. The
commutator is generically nonzero on the zero-sum plane: for r=e0−e1,
r2=0 and r[K_m,E]=(K_m(0,2)−K_m(1,2))w, where

\[
 K_m(0,2)-K_m(1,2)=
 \frac{v_mX_2[(\beta_0-\beta_1)X_0+
 u_m(\beta_0\alpha_1-\beta_1\alpha_0)X_1]}{L_{m0}L_{m1}}. \tag{T13}
\]

Both numerator coefficients cannot vanish for positive invertible G,
since then rows zero and one coincide. This does not say a particular
marked seed has residue e0−e1. It excludes an ambient commutation identity;
a valid induction must control the actual seed commutator in T12.

The independent review checked ambient preservation, the finite-part
projection, all kernel and dimension counts, inherited raw independence,
and the transport identities. The local script
`exploration/source24_terminal_peeling.py` checks raw and normalized append,
the marked-seed correction, and the actual seed pair commutator in six
finite-field fixtures (prefix lengths 2, 3, 4, each with economic and
independent times). It also checks T4 coefficientwise over the rationals.
The run took 0.758 seconds and 20,004,864 bytes maximum RSS; its saved
results are `exploration/source24-terminal-peeling-results.json`.
The primary researcher reviewed the implementation and its scope.

The sharper [append commutator analysis](SOURCE24_APPEND_COMMUTATOR.md)
proves that this discrepancy has generic rank 3q in each coordinate sector
for q>=2, and rank 9q combined for odd q>=5 under the audited incoming
theorem. These are ranks before the completion quotient. The all-length
boundary determinant remains open. No Lean theorem or finite check of
the full recursive annihilator is asserted here.

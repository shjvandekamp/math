# Even-length physical polar correction

**Status: independently audited conditional paper formula, with local exact checks; not Lean formalized.**
This records the substantive formulas returned by the user-authorized
[GPT-6 Pro discussion](https://chatgpt.com/c/6ad127e0-98fc-83eb-bc47-19e34edebd7a).
The formula has subsequently passed two independent local mathematical
audits and an independently implemented physical polar check. The common-G
physical normalizations are H1–H5 in SOURCE24_INDUCTION.md. The formula
applies to even m with binary corank two and projected first-jet completion.
It does not prove incoming or mapped independence.

## A common first-jet pencil

Write G=(1,alpha,beta), a_tc=alpha_c u_t, b_tc=beta_c v_t, and
L_tc=X0+a_tc X1+b_tc X2. In chart X1=1, set

\[
 z_{uc}=-a_{uc}/b_{uc},\qquad
 x_{uc}(\delta)=(-\delta,1,z_{uc}+\delta/b_{uc}). \tag{E1}
\]

For the actual move-first word pi_s=(s,remaining increasingly), split
pi_s=U u V and form its old-line residue

\[
 \mathcal R^s_{uc}(\delta)
   =[K_U e_c^{\mathsf T}v_{uc}K_V]_{X=x_{uc}(\delta)}. \tag{E2}
\]

Only blocks other than u are ordinary kernels. Define

\[
 \mathscr M_{(u,c),(s,b)}(\delta)
   =\sigma_b(\delta)(\mathcal R^s_{uc}(\delta))_{b2},\quad
 (\sigma_0,\sigma_1,\sigma_2)=(-1,1,z_{uc}+\delta/b_{uc}). \tag{E3}
\]

Order rows by c=0 then c=1,2 and columns by b=0 then b=1,2:

\[
 \mathscr M(0)=\begin{pmatrix}D&0\\C&M\end{pmatrix},\qquad
 \mathscr M'(0)=\begin{pmatrix}*&E\\*&M_1\end{pmatrix}. \tag{E4}
\]

D is diagonal, D_uu=a_u0 prod_(j!=u) d_j(z_u0), where d_j is the binary
kernel determinant on X0=0. More generally, with pi_s=U u V,

\[
 (\mathcal R^s_{uc}(0))_{b2}
 =-a_{uc}d_V(z_{uc})(K_U^0(z_{uc}))_{bc}. \tag{E5}
\]

Choose right and left kernel bases R (2m by 2) and L (2 by 2m) for M.
Define Omega=M1−C D^-1 E and Gamma=L Omega R. The formula requires
rank M=2m−2 and det Gamma!=0.

## Right-hand side and physical constant coefficients

For A=1,2 and increasing deletion word P^t, define

\[
 q^{tA}_{uc}=X_A\left[
  \operatorname{Res}_{L_{uc}}
     \frac{(e_1-e_0)P^t}{L_{tA}}
  \right]_2\bigg|_{X=(0,1,z_{uc})};\qquad q^{t0}=0. \tag{E6}
\]

If u=t,c=A, remove the denominator L_tA and use the ordinary P^t.
If u=t,c!=A the value is zero. If u!=t use the residue product of P^t
and divide by the nonzero L_tA. With cvec=c_tA e_r(t) from H4,
the state-zero equation is q0=D cvec. Then set

\[
 \theta=\Gamma^{-1}L(q_{\rm bin}-C\,cvec),\qquad
 \kappa=R\theta,\qquad
 \ell=cvec-D^{-1}ER\theta. \tag{E7}
\]

For incoming (t,N,A,B), the physical constant coefficient is
zero outside new-line sector a=B and, inside that sector,

\[
 \lambda^{(0)}_{(N,s,B,b);(t,N,A,B)}
 = A_t(A,B)\begin{cases}\ell_s,&b=0,\\\kappa_{s,b},&b=1,2.\end{cases} \tag{E8}
\]

The pencil is shared by the three sectors after their known scaling.
Its basis-independent constant operator on any q is

\[
 \binom\ell\kappa=
 \binom{D^{-1}q_0}{0}
 +\binom{-D^{-1}ER}{R}
       \Gamma^{-1}L(q_{\rm bin}-CD^{-1}q_0). \tag{E9}
\]

## Bridge to the physical polar system

On the new line h, put delta=alpha_h epsilon. The actual old–new point is
X2=(delta−a_uc)/(b_uc−beta_h epsilon^3),
X0=−delta−beta_h epsilon^3 X2. Thus X=x_uc(delta)+O(epsilon^3).
The old-vector polar-coordinate functional on a zero-sum row z is

\[
 \operatorname{pol}(z)=
 \frac{z\eta_h}{(b_{uc}-\beta_h\epsilon^3)X_2},\qquad
 \eta_h=e_2^{\mathsf T}
       -\frac{\beta_h\epsilon^3X_2}{X_0}e_0^{\mathsf T}. \tag{E10}
\]

It is one on v_uc and zero on v_Nh. After canceling the common row
factor −X_h/[(b_uc−beta_h epsilon^3)X2], the shared physical columns are
X_b Res(P_s) eta_h, while the incoming side is
A_t(A,h) X_A Res(v_Nh P^t/L_tA) eta_h. The expansions are

\[
 X_0/\delta=-1+O(\epsilon^2),\quad
 \eta_h=e_2^{\mathsf T}+O(\epsilon^2),\quad
 v_{Nh}/\delta=e_1-e_0+O(\epsilon^2). \tag{E11}
\]

The resulting physical equation is

\[
 [\mathscr M(0)+\delta\mathscr M'(0)+O(\delta^2)]
 \begin{pmatrix}\delta I_m&0\\0&I_{2m}\end{pmatrix}
 \binom{\lambda_0(\delta)}{\lambda_{\rm bin}(\delta)}
 =\delta A_t(A,h)q+O(\delta^2). \tag{E12}
\]

Analyticity from H1 gives M kappa=0, D ell+E kappa=q0,
C ell+M1 kappa+M b1=qbin. Eliminating ell and applying L yields E7.
If A=0 the right side starts one order later, giving zero constants.

For direct first-jet implementation, at row(u,c), put g=b_uc and
l_ja=a_ja+b_ja z_uc. For j!=u,

\[
 \dot K_j(a,:)=\frac{(-1,0,b_{ja}/g)}{l_{ja}}
       -\frac{b_{ja}/g-1}{l_{ja}}K_j^0(a,:),\qquad
 \dot v_{uc}=(-1,0,1). \tag{E13}
\]

Use the ordinary ordered-product rule and sigma2'=1/b_uc to obtain E,M1.

## Corrected scalar incoming family

For w=e2 G^-1, the direct leading scalar is

\[
 f^{even}_{tAB}=A_t(A,B)\frac{X_B}{X_2}
 \left[-\frac{X_AX_0}{L_{tA}}(P^t)_{02}
       +X_0\sum_s\ell_s(P_s)_{02}
       +\sum_{s,b=1,2}\kappa_{s,b}X_b(P_s)_{b2}\right]. \tag{E14}
\]

Z_even is the old double-residue matrix of f_even w. Let J=D^-1 E R and

\[
 \Phi_j=\sum_{s,b=1,2}R_{(s,b),j}X_b(P_s)_{b2}
           -X_0\sum_sJ_{sj}(P_s)_{02}. \tag{E15}
\]

Then f_even=f_sparse+A_t(A,B)(XB/X2) sum_j theta_j Phi_j, where f_sparse
is H5 used formally at even m. In particular the formula implies
rank(Z_even−Z_sparse)<=6. The six correction columns are
rho[(XB/X2) Phi_j w], B=0,1,2 and j=1,2.

On the coordinate axis, MR=0 removes all binary old-line poles of Phi_j;
binary starts create no row-zero pole. The resulting pole-free homogeneous
linear form vanishes at X2=0 and takes the value eta_j X2 at X1=0, where
eta_j=sum_s R_(s,2),j. Hence Phi_j(0,X1,X2)=eta_j X2. Consequently
Psi_j=(Phi_j−eta_j X2)/X0 has no added coordinate pole, and an equivalent
old-pair-residue scalar is

\[
 \widetilde f^{even}_{tAB}
 =A_t(A,B)\frac{X_BX_0}{X_2}
 \left[-\frac{X_A}{L_{tA}}(P^t)_{02}
       +c_{tA}(P_{r(t)})_{02}+\sum_j\theta_j\Psi_j\right]. \tag{E16}
\]

This last equality is modulo old double residues, since the removed row
is polynomial. The actual mapped leading operator remains −B0 O^-1 Z_even.

## Independent review and local finite checks

The kernel/cokernel reviewer checked E4–E9 and E15–E16, including the
constant-block signs, q0=D cvec, basis invariance, and coordinate-pole
cancellation. A separate reviewer checked E10–E14 against the actual
physical source system, including sector zero and the extra order when
A=0. The primary researcher checked both derivations and the implementation.

D is invertible under the displayed binary/axis hypotheses. With binary
corank two, Gamma is exactly the projected first-kernel-derivative matrix
after eliminating D. E10–E12 identify it with the even physical polar
first jet, up to nonzero sector factors delta=alpha_h epsilon. Thus the
formula can invoke the previously audited H1 polar hypotheses. Any generic
nonvanishing conclusion for Gamma uses that earlier polar theorem, not the
finite checks alone.

The locally written `exploration/source24_even_correction.py` uses dual
arithmetic for E1–E7 and separately constructs the original physical polar
source blocks at full old–new intersections. A precision-tracked Laurent
inverse and physical rescaling reproduce every lambda0 entry in all three
sectors at m=2 and m=4, with absolute precision at least five. This second
calculation does not use the candidate first-jet pencil.

The common fixture is G=[[1,2,3],[1,5,7],[1,11,13]], time factors
(1,2),(3,5),(7,17),(13,43), and prime 1000003. The saved exact ranks are:

| m | O | B0 | Z_even | B0 O^-1 Z_even | correction | Gamma |
|---:|---:|---:|---:|---:|---:|---:|
| 2 | 18 | 14 | 7 | 6 | 6 | 2 |
| 4 | 108 | 36 | 36 | 36 | 6 | 2 |

The actual equation OY=Z and the six-column correction factorization pass.
The bounded run completed in 0.834 seconds with 21.25 MiB maximum RSS.
E14's incoming matrix was not independently rebuilt by full regular Laurent
elimination, and E16 was audited mathematically rather than tested by this
script. No downloaded implementation was run. These finite ranks do not
prove all-even-m incoming rank or mapped injectivity.

## A uniform lower bound and a six-dimensional remaining test

The auxiliary sparse family in (H5) is defined at even m as well.
The six boundary pivots (H13)--(H15) use only m>=5. The remaining
deletion-word argument (H16)--(H17) uses the all-k theorem with
k=m-1>=4. Neither auxiliary proof requires odd parity; parity entered
when identifying the sparse family with the actual leading operator.
Consequently Z_sparse has generic full column rank 9m for every
even m>=6. Combining this with the six-column correction in (E15)
proves the uniform incoming bound

\[
 \operatorname{rank}Z_{\rm even}\ge9m-6
 \qquad(m\ge6\text{ even}).
 \tag{E17}
\]

This uses the generic even polar first-jet theorem to define the
correction coefficients. It does not require the old source matrix O.
It also does not promote the finite m=4 calculation into an induction
base for a different theorem.

Write the actual correction as Z_even=Z_sparse+C Theta, with C
having six columns. Choose a parameter-only left inverse A of
Z_sparse on a full-rank open. The possible dependency space of
Z_even is isomorphic to the kernel of the six-column map

\[
 y\longmapsto
 \begin{pmatrix}
  (I-Z_{\rm sparse}A)Cy\\
  (I_6+\Theta AC)y
 \end{pmatrix}.
 \tag{E18}
\]

Indeed, for Z_even x=0 put y=Theta x. Multiplying by A gives
x=-ACy, and substitution gives both equations in (E18).
Conversely those equations imply Z_even(-ACy)=0 and
Theta(-ACy)=y, so the two constructions are inverse. In particular
every nonzero dependency has a nonzero six-vector y.
The sufficient condition det(I_6+Theta AC) nonzero is stronger than
the exact injectivity criterion (E18). The shared-new first-jet
nonvanishing theorem alone establishes neither of these conditions.
Even if (E18) is injective, the later actual source-prefix projection
still has to be handled. These implications were independently audited
as paper algebra; no new finite calculation or Lean proof is claimed.

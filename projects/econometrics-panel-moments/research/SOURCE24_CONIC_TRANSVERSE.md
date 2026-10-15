# Transverse pivots for a conic append

**Status: independently audited paper derivation; not Lean formalized.**
The user-authorized [GPT-6 Pro investigation](https://chatgpt.com/c/6ad13838-08fc-83ed-aa54-8025b249a045)
supplied the uniform 9n−6 block below. The primary researcher checked its
normalizations, endpoint support and retained Schur corrections. No
all-length source nonvanishing is asserted.

Assume n>=1, distinct positive alpha values, and distinct positive old
nodes q_ta=alpha_a b_t. Use nonzero append parameters outside all collision
loci. Invertibility of O_n is an additional hypothesis only for CT8.

Use n old conic blocks and append block m=n+1 with b_m=epsilon.
At its state-c line put x=alpha_c epsilon, and parametrize that line by
X(x,y)=(xy,−x−y,1). Let

\[
 v_x=(xy,-x(x+y),x^2),\qquad h_x=(x,0,-y)^T,
 \quad \tau(z)=\frac{zh_x}{(y-x)X_c},\quad \eta(z)=z_2/x^2. \tag{CT1}
\]

At each new/old node y=q_ta these are invertible coordinates on the
zero-sum residue plane: tau(v_x)=0 and eta(v_x)=1. Every interior
completed word ends in K_m, so its new-line residue is proportional to
v_x. Thus tau annihilates all old source columns exactly. The longitudinal
old-column entry is
−[(L_ud Qhat_i^(n))_c](P_(x,q_ud)); it is generally nonzero.

Let P_s use all old blocks, move-s-first, and let P^t use the increasing
old word with t omitted. Ordinary one-variable residues at y=q_ua give
the exact transverse entries of the two new source types:

\[
 \tau\rho F_{m,s,c,b}
   =\operatorname{Res}_{y=q_{ua}}[v_{x,b}e_bP_sh_x],\qquad
 \tau\rho F_{t,m,A,c}
   =\operatorname{Res}_{y=q_{ua}}
     \left[\frac{X_Aq_{tA}^c}{(q_{tA}-x)(q_{tA}-y)}v_xP^th_x\right].
 \tag{CT2}
\]

The signs follow from L(q)(X(x,y))=(q−x)(q−y) and the minus completed
term in F. Each new column has support in just its state-c sector.

## A uniform controlled outgoing block

Normalize outgoing columns as C_s0=F_msc0/x, C_s1=F_msc1/x,
C_s2=F_msc2/x². Their transverse entries extend analytically to x=0.
Write r_t=q_t0, beta_t=q_t1, gamma_t=q_t2. At x=0 the binary kernels are

\[
 B_t(y)=\begin{pmatrix}-y/(\beta_t-y)&\beta_t/(\beta_t-y)\\
                         -y/(\gamma_t-y)&\gamma_t/(\gamma_t-y)\end{pmatrix},
 \quad d_t(y)=\frac{(\beta_t-\gamma_t)y}{(\beta_t-y)(\gamma_t-y)}.
\]

Let f_s be the output-two entry from state one of the actual move-first
binary product and D=prod d_t. The limiting scalar residue functions of
the normalized columns are respectively

\[
 -y^2(P_s(0,y))_{02},\qquad y^2f_s,\qquad -y(f_s+D). \tag{CT3}
\]

At a state-zero node r_t, only C_t0 has a pole. Its pivot is
delta_t=r_t³ prod_(j!=t) d_j(r_t), nonzero under the conic geometry.
This supplies n pivots per sector.

Set Q(y)=prod_t(y−beta_t)(y−gamma_t) and
T_s=Q(f_s−f_1), for s=2,...,n. These polynomials have support

\[
 T_s=\ell_s y^{n-s+1}+\cdots+h_s y^{n+s-1},\quad
 \ell_s=Q(0)(\gamma_{s-1}^{-1}-\gamma_s^{-1})
          \prod_{j>s}\frac{\beta_j-\gamma_j}{\beta_j\gamma_j},\quad
 h_s=(\beta_s-\beta_{s-1})\prod_{j>s}(\beta_j-\gamma_j). \tag{CT4}
\]

To prove the endpoints, the move-s-first and move-one-first words share
the suffix B_(s+1)...B_n. Their prefix difference is zero-sum and is
multiplied by the scalar product of the suffix determinants. For a prefix
of length at least two, the first-order expansion at zero depends only on
its last block, as 1+y/gamma_last+O(y²). At infinity it is
−beta_last/y+O(y^−2). The two last blocks are s−1 and s, yielding CT4.
Every endpoint is nonzero for distinct positive old nodes.

Use outgoing differences A_s=C_s2−C_12 and B_s=C_s1−C_11.
On binary-node transverse rows apply the invertible interpolation map

\[
 \mathcal I(r)(y)=\sum_{z\in\{\beta_t,\gamma_t\}}
                 \frac{r_z}{z^2}\frac{Q(y)}{y-z}. \tag{CT5}
\]

The limiting columns become −T_s/y and T_s. Select coefficient rows
n−s and n+s−1. Their diagonal two-by-two block is diag(−ell_s,h_s);
every earlier pair has support strictly inside these two exponents.
Together with the state-zero pivots this gives, per sector,

\[
 \Delta_n=(-1)^{n-1}\prod_t\delta_t\prod_{s=2}^n\ell_sh_s\ne0.
 \tag{CT6}
\]

For all three sectors the controlled matrix H has size 9n−6 and
det H(epsilon)=Delta_n³+O(epsilon). The remaining outgoing columns are
C_11,C_12 in each sector. Their interpolated limiting representatives are
N_1=Qf_1 and (Q−N_1−c_D y^n)/y, where c_D=prod(beta_t−gamma_t).
The second is polynomial because N_1(0)=Q(0). Eliminating the outer
CT4 coefficients leaves only degrees n−1 and n. This explicitly specifies
the two-dimensional outgoing remainder.

For the undifferenced state-two column, the divided-residue function
−(f_s+D)/y has the additional principal part −1/y at zero. Adding 1/y
removes that pole without changing any binary-node residue. The result
(1−f_s−D)/y is proper and regular at zero, so CT5 gives its product
with Q without a polynomial ambiguity. For the difference columns this
principal part cancels directly.

## Exact remaining Schur matrix

Order columns as old, controlled outgoing, and remaining new. Order rows
as old/old, controlled transverse, remaining transverse, longitudinal.
The transformed matrix is

\[
 \begin{pmatrix}
 A&B_p&B_r\\0&H&J\\0&H_0&J_0\\C&D_p&D_r
 \end{pmatrix}. \tag{CT7}
\]

At an old/old node the old-column residue is its former residue multiplied
by K_m. Thus A is invertible whenever O_n is, and
det A=det O_n times the product of det K_m over all old/old nodes.
The block C is the explicit longitudinal contribution described after CT1.
Eliminating A and H gives the square remaining matrix

\[
 \mathcal R_n=\begin{pmatrix}
 J_0-H_0H^{-1}J\\
 D_r-CA^{-1}B_r-(D_p-CA^{-1}B_p)H^{-1}J
 \end{pmatrix},\qquad \dim\mathcal R_n=9n+6. \tag{CT8}
\]

Its determinant, multiplied by det A det H, is the transformed full
determinant. Both old-node correction terms remain. Only H was evaluated
at epsilon=0; A^-1 may have poles there. Neither boundedness of A^-1 nor
nonvanishing of det R_n is assumed. This is a conditional induction
criterion, not its conclusion.
In particular O_3 is singular throughout the conic family, so CT8 does
not supply the conic three-to-four-block step.

## Connection to the existing binary parity theorem

The primary researcher observed a further identification, independently
checked by a second Astra researcher. Before taking differences, CT5 sends the binary
outgoing columns to Q f_s and Q r_s/y, where r_s is the opposite
off-diagonal entry of the binary product. Indeed
1−f_s−D=r_s. With w=−1/y the binary kernels are precisely the established
common-rho family, c_t=beta_t and rho=gamma_t/beta_t=alpha2/alpha1.
The two function lists become q(P_s) and −w r(P_s), up to the common
nonzero Q. Their residue representation is injective by the regular
interpolation argument. Hence the known rank theorem gives total
outgoing transverse rank 9n at the limit for odd n and 9n−6 for even n.
This does not settle the even correction or CT8.

An independent Astra reviewer checked CT1–CT8, including ordinary-residue
signs, endpoint coefficients, interpolation, all block dimensions and both
old-node corrections. The determinant identities refer to the explicitly
transformed and consistently ordered matrix. The existing binary parity
theorem applies for n>=2 with its stated common-rho hypotheses; the
one-block binary pair is directly independent.

# An axis and matching recurrence for the mixed append jet

**Status: independently audited paper reduction; not Lean formalized.**
The [Pro16 investigation](https://chatgpt.com/c/6ad14d75-dd40-83ed-9250-c0323163bb5d)
proposed the reduction below, which the local researchers checked independently.
It addresses the exact mixed-jet problem
in [the raw quotient note](SOURCE24_RAW_QUOTIENT.md), RQ40. It does not
prove that the new-line observations eliminate every surviving solution.
All original source coefficients remain constant in the effect variables.

## Actual ordered insertions and the common correction

Put r=q−1 and index the adjacent edges by k=1,...,r. Use the RQ37
increment Delta_k=D_(k+1)−D_k, and set

\[
 J=\operatorname{diag}(X/L)G,\qquad
 S=\operatorname{diag}(X/L_N)A_N,\qquad
 T_k=\operatorname{diag}(X)\Delta_k\operatorname{diag}(X)^{-1}.
 \tag{AR1}
\]

The last expression is evaluated through its cancelled rational formula.
For constant outgoing and incoming coefficient matrices x_k,y_k, define

\[
 \alpha_k=\sum_{a,b}x_{k,ab}S_{ab}e_b,\quad
 \beta_k=\sum_{a,b}y_{k,ab}J_{ab}e_b,\quad
 \dot\beta_k=\sum_{a,b}y_{k,ab}(T_k)_{ab}e_b.
 \tag{AR2}
\]

Divide each actual raw row on the right by diag(X). Its outgoing
column is S_ab e_b times the move-first old J word; its incoming
column is (J_t)_ab e_b S times the ascending old word omitting t.
Differentiating those exact words gives

\[
 \dot B_k=(\alpha_kT_k+\dot\beta_kS)J^r
       -(\alpha_kJ+\beta_kS)J^{k-1}T_kJ^{r-k}.
 \tag{AR3}
\]

The incoming prefix derivative is the term dot(beta_k) S J^r. It
cannot be dropped. Two further constant coefficient matrices define
alpha_*,beta_* as in AR2. The common leading column combination is
B_*=(alpha_* J+beta_* S)J^r. Therefore the first-jet relation modulo
the leading image uses

\[
 B^\dagger=\sum_k\dot B_k-(\alpha_*J+\beta_*S)J^r.
 \tag{AR4}
\]

The same two common coefficient matrices must be used on all three
axes and all new-line observations.

## The spectral reduction on one coordinate axis

Fix X_c=0, write i<j for the other states, and choose X_i=1,X_j=z.
On this axis row c of J and T_k is identically zero; this is also the
regular extension at L_c=0. Define

\[
 D_c=(G_{ii}+G_{ij}z)(G_{ji}+G_{jj}z),\quad
 \kappa_c=G_{ii}G_{jj}-G_{ij}G_{ji},\quad
 \lambda=\frac{\kappa_c z}{D_c}.
 \tag{AR5}
\]

The eigenvalues of J are 1,lambda,0. Over the rational function field,
where their differences are nonzero, its projectors are

\[
 \Pi=\frac{J^2-\lambda J}{1-\lambda},\qquad
 \Theta=\frac{J^2-J}{\lambda(\lambda-1)},\qquad
 \Omega=I-\Pi-\Theta.
 \tag{AR6}
\]

Thus J^n=Pi+lambda^n Theta for n>=1. Since JX=SX=X, T_kX=0,
and the image of T_k lies in the active coordinate plane,

\[
 S\Pi=\Pi,\qquad T_k\Pi=0,\qquad \Omega T_k=0.
 \tag{AR7}
\]

For k<r these identities give

\[
 \begin{split}
 T_kJ^r-J^kT_kJ^{r-k}
   &=(\lambda^r-\lambda^{r-k})\Pi T_k\Theta,\\
 J^{k-1}T_kJ^{r-k}
   &=\lambda^{r-k}\Pi T_k\Theta
      +\lambda^{r-1}\Theta T_k\Theta.
 \end{split}\tag{AR8}
\]

The second identity includes k=1 because Omega T_k=0. At k=r,
the terms involving T_r Omega must be retained.

Let a_c=A_N^-1 e_c, s_(c,k)=(alpha_k+beta_k)X, and let the
increment direction be w_k=(0,deltaTau_k,deltaNu_k). Put
eta_(c,k)=w_(k,j)−w_(k,i). Then

\[
 \Pi T_k\Theta a_c=\eta_{c,k}X\vartheta_c(z).
 \tag{AR9}
\]

An explicit scalar is obtained by writing A_N=G diag(s_0,s_1,s_2),
n^(c)=G^-1 e_c:

\[
 \begin{split}
 \psi_c(z)&=z n_i^{(c)}(s_c^{-1}-s_i^{-1})
                    +n_j^{(c)}(s_j^{-1}-s_c^{-1}),\\
 \vartheta_c(z)&=
 \frac{G_{ij}G_{ji}(1+\lambda)}{D_c(1-\lambda)}\psi_c(z).
 \end{split}\tag{AR10}
\]

For verification, the active part of the left eigenvector of J at 1,
normalized against (1,z), is
(G_ji L_i,G_ij L_j)/(D_c(1−lambda)). The active derivative for
w_j−w_i=1 is the column
(G_ii G_ij/L_i², z G_ji G_jj/L_j²) times (−z,1).
The product of that left eigenvector and column is
G_ij G_ji(1+lambda)/(D_c(1−lambda)). Also
(−z,1) Theta a_c=psi_c, using
Omega=(G^-1 e_c)e_c^T/(G^-1)_cc. This proves AR9–AR10.

For the fixed positive fixture
G=((1,2,7),(1,5,3),(1,11,13)), s=(1,2,3), and the quadratic
old-time direction, the entries are

| c | eta_(c,k) | psi_c(z) |
|---:|---:|---|
| 0 | 2k | −(5z+4)/54 |
| 1 | 2k+1 | (1−17z)/36 |
| 2 | 1 | (29z+1)/81 |

They are nonzero. For the common increment (1,3), the three weights
are instead 2,3,1, independently of k; the same reduction applies.

## The complete axis equation and its forcing

The actual axis condition is (B^dagger a_c)|_(X_c=0)=0.
Expanding AR3–AR8, including the last edge, gives

\[
 \mathcal A_c=\mathscr B_{c,0}+\lambda^r\mathscr B_{c,1}
      +\lambda^{r-1}\mathscr B_{c,2}
      -\vartheta_c\sum_{k=1}^r
          \eta_{c,k}\lambda^{r-k}s_{c,k}=0,
 \tag{AR11}
\]

where

\[
\begin{split}
\mathscr B_{c,0}
 &=\left[\sum_k\dot\beta_k\Pi
    -(\alpha_r+\beta_r)\Pi T_r\Omega
    -(\alpha_*+\beta_*)\Pi\right]a_c,\\
\mathscr B_{c,1}
 &=\left[\sum_k(\alpha_k\Pi T_k\Theta+\dot\beta_kS\Theta)
    -\alpha_r\Theta T_r\Omega
    -(\lambda\alpha_*+\beta_*S)\Theta\right]a_c,\\
\mathscr B_{c,2}
 &=-\left[\sum_k\beta_kS\Theta T_k\Theta
               +\beta_rS\Theta T_r\Omega\right]a_c.
\end{split}\tag{AR12}
\]

The dot(beta) terms retain the incoming prefix. The Omega terms retain
the endpoint correction, including r=1. There are no growing matrix
powers in these three forcing expressions. Their dependence on interior
edges is through the four weighted sums of x_k and y_k by deltaTau_k
and deltaNu_k, together with the separately retained final edge and
common-column coefficients.

## Two polynomial recurrences with constant coefficient variables

Put

\[
 D_{N,c}=(G_{ii}s_i+G_{ij}s_jz)(G_{ji}s_i+G_{jj}s_jz),
 \qquad f_c=\frac{z^2}{D_cD_{N,c}}.
 \tag{AR13}
\]

Each s_(c,k) has numerator degree at most 5 over D_c D_(N,c).
For the fixed fixture the four active old/new roots are distinct.
Each orientation's four active entries span linear polynomials plus
one simple-pole term at each of its two roots. Their sum is the
six-dimensional space with numerator degree at most 5 over the common
degree-four denominator. This concerns one axis only; the variables
on different axes are still induced by the same x_k,y_k.

Write d0=G_ii G_ji, d1=G_ii G_jj+G_ij G_ji,
d2=G_ij G_jj, chi=d0/d2 and x=lambda^-1. Then

\[
 z+\chi/z=(\kappa_c x-d1)/d2.
 \tag{AR14}
\]

The involution z↦chi/z fixes x and the rational field extension has
degree two. Consequently there are unique polynomials U_(c,k),V_(c,k)
of degree at most two, with parameter-only constant coefficients, such
that

\[
 s_{c,k}(z)=f_c(z)
          \{U_{c,k}(x)+zV_{c,k}(x)\}.
 \tag{AR15}
\]

Indeed, s/f=N(z)/z² lies in span{z^-2,z^-1,1,z,z²,z³}. If
w=z+chi/z, the identities

\[
 z^{-1}=(w-z)/\chi,\quad
 z^{-2}=(w^2-wz-\chi)/\chi^2,\quad
 z^2=wz-\chi,\quad
 z^3=(w^2-\chi)z-\chi w
\]

give precisely K[w]_(<=2) plus z K[w]_(<=2). The affine change
AR14 and the degree-two field extension prove existence and uniqueness.
The six coefficients are constant-linear functions of x_k,y_k.

Decompose the complete forcing in the same field basis:

\[
 R_{c,0}(x)+zR_{c,1}(x)=
 \frac{x^{r-1}\mathscr B_{c,0}+x^{-1}\mathscr B_{c,1}
                    +\mathscr B_{c,2}}{\vartheta_cf_c}.
 \tag{AR16}
\]

The axis condition is exactly equivalent to

\[
 \sum_{k=1}^r\eta_{c,k}x^{k-1}U_{c,k}=R_{c,0},\qquad
 \sum_{k=1}^r\eta_{c,k}x^{k-1}V_{c,k}=R_{c,1}.
 \tag{AR17}
\]

The right sides initially are rational functions. Their finite poles
must cancel and their polynomial degree must be at most r+1; these
conditions cannot be discarded. Once imposed, the coefficient equation
for U, written U_k=u_(k,0)+u_(k,1)x+u_(k,2)x², is

\[
 \eta_{c,n+1}u_{n+1,0}+\eta_{c,n}u_{n,1}
        +\eta_{c,n-1}u_{n-1,2}=[x^n]R_{c,0},
       \qquad 0\le n\le r+1,
 \tag{AR18}
\]

with out-of-range terms zero; V has the same recurrence. The
rational decomposition needs no square roots: for R(z), set
z^iota=chi/z and use
R1=(R(z)−R(z^iota))/(z−z^iota),
R0=(z R(z^iota)−z^iota R(z))/(z−z^iota).
These are invariant rational functions of x.

When the positional transform has zero right side and every eta is
nonzero, its exact kernel is

\[
 \eta_{c,k}U_{c,k}=A_{c,k-1}-xA_{c,k},\qquad
 \eta_{c,k}V_{c,k}=B_{c,k-1}-xB_{c,k},
 \tag{AR19}
\]

where A_k,B_k are linear polynomials for 1<=k<=r−1 and their
indices 0 and r are zero. Telescoping proves sufficiency. Conversely,
the first constant coefficient forces U_1 divisible by x; dividing
successive residual identities constructs the linear A_k and the last
identity gives the right endpoint. The same argument applies to V.
Thus this positional transform has a 4(r−1)-parameter kernel. This is
not the dimension of the actual source kernel: its forcing and the
other observations depend on the same original coefficient matrices.

## The local matching equations evaluate the same variables

At the regular matching point X_c=0, X_i=1,
z=z_c=−G_ci/G_cj, let g_c=G(c,:) and define

\[
 \sigma_k=\alpha_kJ+\beta_kS,\quad
 \omega_{c,k}=\sum_b y_{k,cb}G_{cb}e_b,\quad
 m_{c,k}=(\alpha_k)_cg_c+\omega_{c,k}S.
 \tag{AR20}
\]

The explicit RQ33–RQ34 matching blocks give exactly

\[
 ([O_k,\widetilde P_k](x_k,y_k))_c
 =m_{c,k}J^ra_c
   -(\sigma_kJ^{k-1}e_c)(g_cJ^{r-k}a_c).
 \tag{AR21}
\]

Since g_cX=0, g_c Pi=0. Write Pi e_c=X ell_c,
h_c=g_c Theta a_c and zeta_c=g_c Omega a_c. The formula for Omega
gives zeta_c=1/s_c and h_c=g_c a_c−1/s_c. At the fixed fixture,

| c | z_c | lambda_c | ell_c | h_c | zeta_c |
|---:|---|---|---|---|---|
| 0 | −2/7 | −448/1479 | 497/1927 | −1/3 | 1 |
| 1 | −1/3 | −9/20 | −213/58 | 5/9 | 1/2 |
| 2 | −1/11 | −11/18 | 781/87 | −2/9 | 1/3 |

Substitution in AR21 gives the exact matching equation

\[
\begin{split}
0={}&m_{c,k}\Pi a_c+\lambda_c^r m_{c,k}\Theta a_c\\
 &-(\lambda_c^{r-k}h_c+\mathbf1_{k=r}\zeta_c)
   \{\ell_c s_{c,k}(z_c)
       +\lambda_c^{k-1}\sigma_k\Theta e_c
       +\mathbf1_{k=1}\sigma_k\Omega e_c\}.
\end{split}\tag{AR22}
\]

Both endpoint terms are necessary when r=k=1. The coefficient of
s_(c,k)(z_c) is nonzero for every r>=1 and 1<=k<=r: for k<r
all of ell_c,lambda_c,h_c are nonzero, while h_c+zeta_c is respectively
2/3,19/18,1/9. Thus AR22 solves for the value

\[
 s_{c,k}(z_c)=f_c(z_c)
       \{U_{c,k}(\lambda_c^{-1})
                          +z_cV_{c,k}(\lambda_c^{-1})\}.
 \tag{AR23}
\]

The three evaluation parameters are −1479/448,−20/9,−18/11.
This is a value condition coupled to m_k and sigma_k, not an assertion
that matching values are independent coordinates of the original edge
space.

## What is still required

The six forced polynomial identities AR17 and the matching equations
AR22 describe exactly the axis and matching part of RQ40. They all use
the same constant x_k,y_k and the same two common coefficient matrices.
After clearing the fixed denominators, length appears through shifts,
weighted sums and powers of the three fixed matching eigenvalues;
the finite rational pole locations do not grow with q.

The actual new-line equations must still eliminate every nonzero solution
of that coupled system. Neither a homogeneous positional kernel count
nor the nonzero matching coefficients proves this. The independently
checked finite first jets, including the common-direction q=3,4 cases,
remain evidence for that open implication, not a uniform theorem.

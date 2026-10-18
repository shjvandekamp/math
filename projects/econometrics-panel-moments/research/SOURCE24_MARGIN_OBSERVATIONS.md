# Terminal-pole data and limitations of endpoint-margin observations

**Status: independently audited paper identities and obstruction theorems,
with external exact finite certificates. No full source-independence proof.**

The [endpoint-margin investigation](https://chatgpt.com/c/6ad19b6a-0878-83ed-b845-3e380f31c2b8)
supplied the terminal-pole identities and a uniform obstruction to recovering
the margins from any fixed order of vertex jets. Local derivations and an
independent review checked both. A separate local exact computation then
disproved the two proposed terminal-pole margin duals generically at
q=4,5,6. The limitations concern arbitrary actual source combinations;
they do not disprove the desired six-column result for the special R_ab.

Use the actual old sources E_ta,F_tsab and endpoint margins from
(LC38)--(LC44) in [the collision note](SOURCE24_LAST_TIME_COALESCENCE.md).
Set m=q-1, A=A_q, D_X=diag(X), H_c={L_qc=0}, and
v_c=A(c,:)D_X. P_s starts with K_s and then contains the other m
earlier kernels in increasing order; T_t is the increasing product
of those m kernels with K_t omitted. Throughout q>=4 and the stated
row forms, coordinates and incidence determinants are generic units.

## An exact terminal-pole boundary map

For j different from c and third state l, define the transverse divided
residue by taking the residue and cancellations before restricting:

\[
 \rho_{cj}(R)=
 \left.\frac{L_{qc}}{X_c}(RD_X^{-1}A^{-1})_j\right|_{H_c}.
 \tag{MO1}
\]

On the actual source family, it kills every E column and every bulk
pair F_tsab with t,s<q. For E_qc the transformed residue is supported
on coordinate c. For a bulk pair the prescribed suffix ends with K_q,
and K_q D_X^(-1)A^(-1)=diag(L_q)^(-1), giving the same support.
The only surviving boundary functions are

\[
 U_{s,e}^{cj}=A(c,e)
   \left[(A^{-1})_{ej}
          -X_e(e_eP_sD_X^{-1}A^{-1})_j\right]_{H_c},
\]
\[
 W_{t,d}^{cj}=-\frac{A_t(d,c)X_d}{L_{td}}
                  (v_cT_tD_X^{-1}A^{-1})_j\big|_{H_c}.
 \tag{MO2}
\]

These are respectively the observations of F_(q,s,c,e) and
F_(t,q,d,c). Hence any actual coefficient combination has

\[
 \rho_{cj}(R)=\sum_{s,e}\alpha_{q,s,c,e}U_{s,e}^{cj}
                  +\sum_{t,d}\alpha_{t,q,d,c}W_{t,d}^{cj}.
 \tag{MO3}
\]

There are no E coefficients or bulk pair coefficients in this identity.
In particular the left side is computed directly from the rational
preimage R_ab in (LC31), without first recovering its source expansion.

Let D_m be the product of all 3m earlier row forms. Each function
in (MO2) has denominator dividing D_m: every earlier block occurs at
most once, and the last kernel cancels the output-coordinate divisions.
Zero sum gives, on H_c,

\[
 L_{qj}\rho_{cj}(R)+L_{ql}\rho_{cl}(R)=0.
\]

The two restricted terminal forms are coprime. Thus D_m rho_cj is
divisible by L_ql, and

\[
 \Phi_{cj}(R)=\left.\frac{D_m}{L_{ql}}\rho_{cj}(R)\right|_{H_c}
 \tag{MO4}
\]

is a homogeneous binary polynomial of degree 3m-1. This gives 3m
coordinates for the 6m actual boundary coefficients in each sector.
The polynomial factors and signs hold separately for every U and W.

At the own matching point p_c=H_c intersect {X_c=0}, the old
denominators remain units. Directly from (MO2),

\[
 U_{s,c}^{cj}(p_c)=A(c,c)(A^{-1})_{cj},\qquad
 W_{t,c}^{cj}(p_c)=0.
 \tag{MO5}
\]

Therefore the outgoing diagonal total sum_s alpha_(q,s,c,c) can
be obtained from rho_cj(R)(p_c) only after subtracting all off-diagonal
boundary contributions in (MO3), then dividing by the nonzero factor
in (MO5). Those terms have not disappeared. Ordinary undivided matching
values would also lose the information retained in this formula.

The terminal-pole map cannot recover the three totals sigma either.
The exact ordered identity

\[
 H_k=E_{1k}+\sum_e F_{1,2,k,e}
       =X_ke_k(I-K_1K_2\cdots K_q)
 \tag{MO6}
\]

has S_(q,k)=sigma_k=1, all other margins zero, and all terminal
transverse residues zero, since its pair terms are bulk terms.

## Exact failure of two proposed boundary duals

A proposed last-pair dual on (MO4) would take value one on
U_(m,c),W_(m,c) and zero on all other boundary columns. A proposed
total-boundary dual would take value one on every U_(s,c),W_(t,c)
and zero on the off-diagonal-state columns. They would recover
S_(q-2,c) and S_(q-2,c)+S_(q-1,c), respectively.

Neither dual exists generically at q=4,5,6. The verifier
`exploration/source24_terminal_boundary_duals.py` uses the actual
ordered formulas (MO2), common matrix
G=((1,1,1),(1,30,10),(1,3,2)), times (8^t,8^(2t)), and prime
1000003. It evaluates the cleared degree-(3m-1) polynomials at 3m
distinct ordinary points on each terminal line. Univariate polynomial
unisolvence makes this evaluation map an isomorphism on the entire
polynomial target, not merely a sampled lower bound.

For every state, the exact ranks are:

| q | Boundary observation | With last-pair target row | With total-boundary target row |
|---|---:|---:|---:|
| 4 | 9 | 10 | 10 |
| 5 | 12 | 13 | 13 |
| 6 | 15 | 16 | 16 |

Matrices, nodes, denominator-valid parameters, target rows and selected
nonzero minors are saved in
`exploration/source24-terminal-boundary-duals-results.json`.
The universal degree bound caps the generic observation rank at 3m.
Each augmented (3m+1)-minor is a nonzero rational parameter function
because its reduction modulo the prime is nonzero. Freeze the chosen
integer chart nodes when considering that minor; their denominators
remain units on a nonempty generic open. The target is consequently
outside the generic row space, proving generic nonexistence of each
dual at the stated lengths. This is stronger than failure at one
singular fixture and does not extrapolate to every q.

Other terminal sectors cannot repair the missing dual: outgoing origin
state c and incoming destination state c partition the boundary columns,
and the other sectors vanish on this sector's columns. Restrictions to
the special six preimages R_ab could still supply additional identities.

## All fixed-order vertex jets can be supplied by local sources

At each vertex e_k use the chart X_k=1, with the other coordinates x,y.
Let J_r record Taylor coefficients through degree r of the two divided
outputs Y_i/X_i,Y_j/X_j, for all three vertices. Its target dimension is
nu_r=3(r+1)(r+2); zero sum determines the remaining divided output.
Define

\[
 d_r=\frac{3r^2+11r+6}{2}.
 \tag{MO7}
\]

For generic common-G parameters and q>=d_r, the actual E_ta columns
alone span this entire jet target. This statement is independent of
old-source independence.

For the proof, put b=A_t(a,i)/A_t(a,k), c=A_t(a,j)/A_t(a,k).
The two divided output coordinates of E_ta are, by source state,

\[
 \begin{array}{c|c}
 a=k&(-b,-c)/(1+bx+cy)\\
 a=i&(1,0)+x(-b,-c)/(1+bx+cy)\\
 a=j&(0,1)+y(-b,-c)/(1+bx+cy).
 \end{array}
 \tag{MO8}
\]

For fixed a and variable time factors U,V, their three-vertex jet
coefficients are Laurent polynomials. The nonconstant exponent pairs
at vertices 0,1,2 lie respectively in the disjoint sets
(p,s), (-p-s,s), (p,-p-s), where p,s>=0 and p+s>0.
The active vertex has parameter degree at most r+1; the other two
have degree at most r, together with one shared constant coefficient.
The number of monomials is

\[
 \left[\binom{r+3}{2}-1\right]
       +2\left[\binom{r+2}{2}-1\right]+1=d_r.
 \tag{MO9}
\]

Their evaluation at q actual times has generic full column rank.
For an explicit positive witness take u_t=2^t and v_t=2^((2r+3)t).
Every exponent pair has coordinates of absolute value at most r+1,
so p+(2r+3)s is different for distinct pairs. The first d_r time
evaluations form a generalized Vandermonde with distinct nonzero
bases z_gamma=2^(p_gamma+(2r+3)s_gamma), and determinant
product_gamma z_gamma times product_(gamma<gamma') (z_gamma'-z_gamma).
Thus actual constant source combinations recover each parameter
coefficient vector, respecting all cross-vertex parameter coupling.

At a fixed vertex and homogeneous degree n, the active-source coefficient
vectors span gradients of degree-(n+1) forms. For n>=1 the inactive
source states also give x times gradients of degree-n forms and y
times those gradients. These span all degree-n vector polynomials:
the kernel of curl(f,g)=partial_x g-partial_y f consists of gradients,
whereas curl(x grad Q)=partial_y Q is onto the degree-(n-1) forms
in characteristic zero. Degree zero is supplied by gradients of linear
forms. The disjoint nonconstant parameter cones separate the vertices,
so an annihilator of all E jets vanishes on every target coordinate.
This proves the asserted full jet rank.

## Arbitrary margins with unchanged bounded-order jets

For q>=4, any nine margin values s_(ell,k) are realized by

\[
 H_s=\sum_k\left[
 s_{q-2,k}F_{q,q-1,k,k}
 +s_{q-1,k}F_{q,1,k,k}
 +s_{q,k}F_{1,2,k,k}\right].
 \tag{MO10}
\]

Each source lies in the indicated actual terminal group. If also
q>=d_r, subtract an E-only combination with the same J_r data.
The resulting Z_s has J_r(Z_s)=0 and S(Z_s)=s, because every E
coefficient has zero F margins. If s_(q,k)=-s_(q-2,k)-s_(q-1,k),
then sigma(Z_s)=0. The exact conservation law (LC40) gives

\[
 V(I_{\rm old}(Z_s))=\mathcal T S(Z_s).
 \tag{MO11}
\]

The fixed-total determinant (LC44) makes this right side arbitrary
in six dimensions. Hence for q>=max(4,d_r), all fixed-order vertex
jets and the three sigma values can stay fixed while the six endpoint
prefix observations vary arbitrarily. As a statement about given
actual coefficient combinations this needs no source independence;
interpreting I_old intrinsically on rational rows uses the old-basis
premise. For example d_0=3,d_1=10,d_2=20,d_3=33.

There is an additional limitation on recovering sigma from combined
data. Apply the same E-only jet cancellation to H_k in (MO6). Since
the terminal-pole map also kills every E, both its data and any fixed
order of vertex jets can be zero while sigma_k remains one.

These theorems exclude universal extraction from those observations.
They do not conflict with uniqueness of source coefficients from the
entire rational row under old independence. A proof for the six special
R_ab must use their additional global constraints, a growing-order
observation, or another actual source-graph identity. None of these
remaining possibilities is claimed here.

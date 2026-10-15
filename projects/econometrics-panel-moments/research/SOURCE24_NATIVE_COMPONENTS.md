# Native components, a regular limit, and terminal extraction

**Status: independently audited paper derivation; not Lean formalized.**
Source: the user-authorized [GPT-6 Pro investigation](https://chatgpt.com/c/6ad12df6-2b64-83ed-898c-45623f243b39).
The primary researcher and an independent Astra reviewer checked N1–N8,
including the regular-frame and saturation arguments. Use the full geometry
and spaces of the binary quotient note. No incoming independence theorem
is claimed.

## Native splitting and the B=2 representative

Suppose R is in W0, Rj/X0 has only old-line poles for j=1,2, and
T_i1 R=T_i2 R=0. Then

\[
 \mathsf P_jR=R_j(e_j-e_0)\in W^{[j]},\qquad
 R=\mathsf P_1R+\mathsf P_2R, \tag{N1}
\]

where W^[j] is the sector in direction ej−e0. The new divided component
is −Rj/X0. On line i=(u,c), write Res(Rj/Xj)=Xc b_ij. Zero binary
feedback makes b_ij/X0 regular at Qi0. For c=0 this supplies the extra
matching zero after changing the component to zero. For c!=0 division
by X0 is regular at the matching point. The other ambient conditions
are inherited. Each seed U_tA meets the hypotheses, so its two native
projections are legitimate moment rows.

The explicit normalized pair basis B20–B22 extends verbatim to j=2:

\[
 \Psi^{[j]}_{ik}
 =\frac{X_0X_j\ell_{ik}(X)}
 {P_0P_j\ell_{ik}(P)L_iL_k}(e_j-e_0). \tag{N2}
\]

Each scalar pair residue is one at its own pair and zero elsewhere.
Let C_21 map Psi^[2] to Psi^[1], preserving scalar pair data.
The explicit incoming lift B17 then satisfies

\[
 F^*_{B2}=w_2\mathsf P_2U+w_1C_{21}\mathsf P_2U,\qquad
 F^*_{B2}-w_2U
 =-\frac1{\det G}\sum_{i<k}(\rho_{ik}U\cdot\alpha)\Psi^{[1]}_{ik}.
 \tag{N3}
\]

The first identity follows from component two and pair data, using
injectivity of scalar pair observations on W^[1]. The second uses
w1 r2−w2 r1=−(r dot alpha)/detG for zero-sum r. Since U belongs to N,
the second expression directly represents its incoming quotient class.
No individual inadmissible subtraction term is reduced modulo N.

## A singular geometric limit with regular representatives

Set

\[
 G(\delta)=\begin{pmatrix}
 1&a+\delta&\beta_0\\1&a_1&\beta_1\\1&a&\beta_2
 \end{pmatrix},\qquad
 (a_1-a)(\beta_2-\beta_0)(a_1\beta_2-a\beta_1)\ne0. \tag{N4}
\]

Use positive parameters and generic time factors. At delta=0, G remains
invertible and w=(−1,0,1)/(beta2−beta0). Same-block lines zero and two
meet on X2=0, so this is outside the earlier full-geometry open set.

For the proposed regular ambient module use the 3m single-block rows
E_i=Xc ec(I−Ku) and the two elementary cross-pair rows at each pair.
At delta=0, generic cross-points remain off the axes with independent
residue-vector pairs; the E_i remain independent by their line poles.
The frame therefore stays independent and has size n+3m. Source and
seed formulas are regular rational families, with each block occurring
at most once, and their coordinates in this frame extend regularly.
One way to justify regular coordinates is to choose ordinary evaluation
functionals giving a nonzero frame minor at delta=0 and invert that
regular minor. The pair bases (N2) also extend, since their denominators
involve only nondegenerate cross-pair data.

Thus (N3) gives the regular limit

\[
 F^*_{tA,B2}(0)=\frac{\mathsf P_2U_{tA}(0)}{\beta_2-\beta_0}.
 \tag{N5}
\]

Over the power-series ring O=F[[delta]], let W_O be this regular framed
module and define N_sat=W_O intersect N_F((delta)). Its reduction
N_flat=N_sat/delta N_sat embeds in W_O/delta W_O by saturation.
If the classes [P1 U_tA(0)] are independent modulo N_flat, the generic
B=2 incoming classes are independent: clear the valuation of a hypothetical
relation and reduce its nonzero leading coefficient modulo delta.
Here [P2 U(0)]=−[P1 U(0)] modulo N_flat: the regular seed U belongs
to N_sat, so its native splitting remains a relation in this flat quotient.

If det O_source(0)!=0, the source rows together with the E_i are a
regular basis. N has a constant coefficient description in that basis,
so it is a direct summand and N_flat equals the specialized generator
span. Neither this invertibility nor the required native-class independence
is established here. This is a conditional criterion, not permission to
replace a flat limit by an ordinary specialized span.

## Explicit terminal extraction

Let m=q+1 with q>=2 and i=(u,c), u<=q. For any ambient row R set

\[
 \mathcal E^{(m)}_{i,d}(R)
 =\left[\frac{\operatorname{Res}_{L_i}(RK_m^{-1})_d}
 {X_cL_{md}}\right]_{Q_{i,d}}
 =\left[\frac{(\operatorname{Res}_{L_i}(R\operatorname{diag}(X)^{-1})A_m^{-1})_d}
 {X_c}\right]_{Q_{i,d}},\qquad
 \mathcal J^{(m)}_{i,b}(R)
 =\frac{\sum_d A_m(d,b)\mathcal E^{(m)}_{i,d}(R)}{A_u(c,b)}.
 \tag{N6}
\]

The second formula for E removes the apparent coordinate poles before
evaluation. The ambient matching factor removes Xc, including d=c.
For actual sources with t,s<=q, t!=s, and full-m long empty rows with t<=q,

\[
 \mathcal J^{(m)}_{i,b'}F_{t,s,a,b}
   =\delta_{i,(t,a)}\delta_{b',b},\qquad
 \mathcal J^{(m)}_{i,b'}F_{t,a}=0. \tag{N7}
\]

Indeed, their completed words end in Km. Multiplying by Km^-1 leaves
the prefix term I_tab Km^-1 minus an old completed product. Every divided
line residue of the latter still has factors Xc and Xd, so it vanishes
after removing Xc and evaluating at Xd=0. The prefix contributes
delta_i,(t,a) At(a,b)(Am^-1)_bd; multiplying by Am proves N7.
For long empty rows the remaining prefix Xa ea Km^-1 is polynomial.

Let W_tail span these interior shared sources and long empty rows, all
still evaluated on the full m-block family. Let N_tail span the corresponding
first-slot differences, long empty rows, and selected output-zero rows,
with block labels at most q. Under final O_m invertible,

\[
 \ker((\mathcal J_{i,1},\mathcal J_{i,2})_{u\le q}|W_{\rm tail})
   =N_{\rm tail}. \tag{N8}
\]

The dimensions are 9q(q−1)+3q for W_tail and 9q(q−2)+6q for N_tail;
N7 gives map rank 6q. Source independence follows from O_m; long empty
independence modulo those rows follows from their single-block corrections.
For old seed labels, J_i0 U_tA=delta_i,(t,A) and its two binary J values
are zero.

The full N has an additional 18q−3 independent generator directions:
first-slot differences involving the final block, final-block shared
output-zero rows, and final-block long empty rows. N8 does not annihilate
or control those directions. Their action on the native incoming classes,
or on their flat limits, remains the unresolved step.

## Extraction on the additional boundary directions

Continue with m=q+1, q>=2. Write M=A_m^-1 and

\[
 \widetilde K_t=\operatorname{diag}(X)K_t\operatorname{diag}(X)^{-1}
              =\operatorname{diag}(X_c/L_{tc})A_t.
\]

For an ordered word P, use tilde P for the product of the corresponding
tilde kernels in the same order. For the raw completed row Qhat define,
at each old line i=(u,c), u<=q,

\[
 g_i^{t,s,a,b}=\frac{\operatorname{Res}_{L_i}
      (\widehat Q_{t,s,a,b}\operatorname{diag}(X)^{-1})}{X_c}.
 \tag{N9}
\]

These rational rows have the explicit form

\[
 g_i^{t,s,a,b}=\begin{cases}
 A_t(a,b)e_b\widetilde P_s^{\widehat t},&u=t,\ c=a,\\
 0,&u=t,\ c\ne a,\\
 A_t(a,b)\dfrac{X_a}{L_{ta}}(\widetilde K_U)_{bc}
                A_u(c,:)\widetilde K_V,
      &u\ne t,\quad P_s^{\widehat t}=K_UK_uK_V.
 \end{cases} \tag{N10}
\]

Empty words mean the identity. Indeed Qhat diag(X)^-1 equals
A_t(a,b) X_a/L_ta e_b tilde P. At the shared pole, removing L_ta
and dividing by Xc=Xa gives the first case. At another block,
Res_Luc tilde K_u=Xc e_c^T A_u(c,:), giving the last case.
Thus the matching factor has been removed before edge evaluation.

For a collection of such rows set

\[
 \mathcal H_{i,b'}(g)=\frac1{A_u(c,b')}
   \sum_{d=0}^2 A_m(d,b')[g_iM]_d(Q_{i,d}). \tag{N11}
\]

Every actual shared source then satisfies

\[
 \mathcal J_{i,b'}F_{t,s,a,b}
 =\delta_{i,(t,a)}\delta_{b',b}-\mathcal H_{i,b'}(g^{t,s,a,b}).
 \tag{N12}
\]

The incidence term is absent when t=m. The prefix contributes
A_t(a,b) M_bd to E_(t,a),d; multiplication by A_m and division by
A_t(a,b') gives the displayed Kronecker coefficient. The completed
term contributes N11 with the minus sign. For interior sources its
last tilde K_m satisfies tilde K_m M=diag(Xd/L_md). Consequently
the d-component vanishes at Q_i,d, including d=c, recovering N7.

For t<=q choose r(t)=min({1,...,q} minus {t}); for shared block m
choose first slot 1. The additional generators of N beyond N_tail have
the exact extraction values

\[
\begin{aligned}
 \mathcal J(F_{t,m,a,b}-F_{t,r(t),a,b})
   &=-\mathcal H(g^{t,m,a,b}),&&t\le q,\\
 \mathcal J(F_{m,s,a,b}-F_{m,1,a,b})
   &=-\mathcal H(g^{m,s,a,b}-g^{m,1,a,b}),&&2\le s\le q,\\
 \mathcal J F_{m,1,a,0}&=-\mathcal H(g^{m,1,a,0}),\\
 \mathcal J F_{m,a}&=-\sum_b\mathcal H(g^{m,1,a,b}).
\end{aligned} \tag{N13}
\]

These hold for all extraction outputs; retain b'=1,2 for the binary
restriction. The last line uses F_ma=E_ma+sum_b F_m1ab and J E_ma=0,
because E_ma has no old-line pole. The counts are
9q+9(q−1)+3+3=18q−3. Under final O_m invertibility these generators
are independent modulo N_tail. Only A_m^-1, not an old-source inverse,
occurs in these formulas.

## Extraction on native seed components

For an old seed U=U_tA, t<=q, and j=1,2, set
R_i^[j]=Res_Li U_j/(X0 Xc Xj). These functions are regular at each
coordinate-edge point; zero binary feedback supplies the extra zero at
X0=0. Substitution in N6 gives

\[
 \mathcal E_{i,d}(\mathsf P_jU)
 =\left[R_i^{[j]}(X_0M_{jd}-X_jM_{0d})\right]_{Q_{i,d}}, \tag{N14}
\]

and therefore

\[
 \mathcal J_{i,b'}(\mathsf P_jU)
 =\frac1{A_u(c,b')}\sum_d A_m(d,b')
   \left[R_i^{[j]}(X_0M_{jd}-X_jM_{0d})\right]_{Q_{i,d}}. \tag{N15}
\]

The formulas remain regular when d=c. N7 gives

\[
 \mathcal J_{\rm bin}(\mathsf P_1U)
   =-\mathcal J_{\rm bin}(\mathsf P_2U). \tag{N16}
\]

These are extraction values, not classes modulo the additional boundary
directions.

## An exact quotient criterion retaining the boundary

Put J=J_binary with 6q outputs. The selected interior source rows give
the explicit right inverse L(e_(u,c,b))=F_(u,r(u),c,b), b=1,2, by N7.
Since N_tail is contained in ker J, the map R to
(JR,[R−LJR]) induces an isomorphism

\[
 \mathscr W_0/N_{\rm tail}\simeq K^{6q}\oplus\overline K,
 \qquad \overline K=\ker J/N_{\rm tail}. \tag{N17}
\]

Here dim W0=9q²+12q+3 and dim N_tail=9q²−12q, so
dim overline K=18q+3 and the full space in N17 has dimension 24q+3.
Let b_1,...,b_(18q−3) be the generators in N13. Define

\[
 J_\partial x=J\sum_\ell x_\ell b_\ell,\qquad
 K_\partial x=\left[\sum_\ell x_\ell b_\ell-\mathscr L J_\partial x\right].
 \tag{N18}
\]

Then the actual quotient is

\[
 \mathscr W_0/N\simeq
  (K^{6q}\oplus\overline K)/\operatorname{im}(J_\partial,K_\partial).
 \tag{N19}
\]

The combined boundary map is injective by independence modulo N_tail.
Writing h=rank J_partial, its second component is injective on
ker J_partial. Projection onto the first factor gives the exact sequence

\[
 0\longrightarrow\overline K/K_\partial(\ker J_\partial)
 \longrightarrow\mathscr W_0/N
 \longrightarrow K^{6q}/\operatorname{im}J_\partial\longrightarrow0.
 \tag{N20}
\]

The two outer dimensions are 6+h and 6q−h, summing to 6m.
Thus pivots in the explicit J_partial can organize the remaining incoming
calculation into these two blocks. Its rank h is unresolved and may equal
6q. No size improvement or incoming independence is asserted.

An independent Astra researcher derived N9–N20 from the audited extraction
formula; the primary researcher checked the conjugation, signs, native
projection formula, and quotient dimension argument before integration.

## Finite checks of the full boundary action

`exploration/source24_terminal_extraction.py` compares actual transformed
source residues with the independently cancelled conjugate-word formula
at every old line and each coordinate edge. It verifies the interior
extraction, full long-empty rows, all four boundary groups, and native
component extraction. At c=d=0, independent second-order source jets
check both vanishing factors before evaluation. The primary researcher
reviewed the implementation.

The saved `exploration/source24-terminal-extraction-results.json` records:

| Old blocks q | Fixture | Boundary columns | Binary extraction rank |
|---:|---|---:|---:|
| 2 | economic | 33 | 12 / 12 |
| 3 | economic | 51 | 18 / 18 |
| 4 | economic | 69 | 24 / 24 |
| 3 | independent time factors | 51 | 18 / 18 |

All calculations are exact modulo 1,000,003, and the full actual source
matrices are invertible in these fixtures. The successful bounded run
took 1.683 seconds and about 20.7 MiB maximum RSS. The nonzero minors
prove generic h=6q separately at these fixed lengths after clearing
denominators. No uniform assertion about h is made.

Here the boundary spans every binary extraction output, so the rightmost
quotient in N20 is zero. All 6m remaining dimensions lie in the leftmost
quotient. Thus these observations alone do not distinguish any full
quotient direction at these fixtures; native incoming independence still
requires the remaining boundary elimination.

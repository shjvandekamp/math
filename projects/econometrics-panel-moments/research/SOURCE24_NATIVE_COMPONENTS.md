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

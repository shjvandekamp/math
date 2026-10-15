# Explicit raw append quotient and a uniform 18-column subfamily

**Status: independently audited paper results; not Lean formalized.** The
full 18q-column boundary rank remains open. The
[GPT-6 Pro investigation](https://chatgpt.com/c/6ad13a68-9e88-83ed-90ba-098f4f9795f8)
proposed these results; the primary researcher and an independent Astra
reviewer checked the quotient kernel, collision argument and witness.

Use the wide ambient Wwide_m of `SOURCE24_RAW_APPEND.md`, of dimension
9m²+3. Its rows have the final-coordinate factors, matching departure
factors, no same-block double residues, and zero-sum cross-pair residues.
Appending the new stochastic kernel K_N, N=q+1, preserves these
conditions and is injective over the rational-function field. Therefore

\[
 \dim(\widehat W_{q+1}/\widehat W_qK_N)=18q+9. \tag{RQ1}
\]

For any H in Wwide_(q+1) put

\[
 B=H\operatorname{diag}(X)^{-1},\quad C=BA_N^{-1},\quad
 R=HK_N^{-1}=C\operatorname{diag}(L_{N0},L_{N1},L_{N2}). \tag{RQ2}
\]

These expressions retain the actual ordered products when H is a source.

## Exact quotient coordinates

At each new/old intersection, with new state c, the double residue of R
has component c zero, because R_c contains L_Nc. Its row sum is zero,
because K_N^−1 1=1. Thus it has one scalar coordinate in the line
{z:z_c=0,sum z=0}. These supply 9q tests. On each new line also retain
the two coefficients of the homogeneous linear polynomial

\[
 \sigma_c=\left.\frac{L_{Nc}R\mathbf1}{X_c}\right|_{L_{Nc}=0}.
 \tag{RQ3}
\]

This is polynomial already on the whole ambient: row sums have no pair
poles, and their single-line residue contains X_c.

The 9q+6 tests vanish exactly when R has no new-line poles. To prove the
nontrivial direction, let r_c=(L_Nc R/X_c)|_L_Nc. Vanishing cross tests
remove its old-line poles; same-block double residues were already zero.
It is consequently a linear polynomial row with component c zero and
row sum zero, so r_c=ell_c(e_i−e_j), for the other two states i,j.
At L_Nc=L_Ni its component i vanishes, and at L_Nc=L_Nj its component j
vanishes, by R_i=C_i L_Ni and the absence of same-block double poles.
The two distinct zeros force the linear form ell_c to vanish.

Next, on each axis X_d=0 take the residues of C_d at its 2q old-line
points with departure state a!=d, and its value at one fixed ordinary
axis point. These 6q+3 functionals are globally defined, before imposing
the first tests. Their sufficiency uses the first tests: once R has no
new poles, C_d=R_d/L_Nd has no new poles on this axis. The possible
L_Nd pole is removed by its departure factor X_d. Old state-d residues
vanish there for the same reason. Therefore C_d restricted to the axis
has only those 2q poles, and residues plus one value determine it.
All these tests vanish exactly when every R_d has its required X_d factor.

Finally retain one matching value per old line:

\[
 \eta_{ta}(H)=
 \left[\left(\frac{\operatorname{Res}_{L_{ta}}B}{X_a}\right)
 A_N^{-1}\right]_a\bigg|_{L_{ta}=X_a=0}. \tag{RQ4}
\]

The quotient by X_a is regular at the matching point by the ambient
departure condition. Once the preceding tests vanish, for output d!=a
the old departure factor remains automatically after dividing R_d by X_d.
For output a, the remaining matching condition is precisely RQ4=0,
since its residue is the displayed coefficient times L_Na, nonzero at
that old matching point. All other ambient conditions are inherited.

Thus these 18q+9 linear functionals define a map T_N with

\[
 \ker T_N=\widehat W_qK_N,\qquad
 \widehat W_{q+1}/\widehat W_qK_N\simeq\mathbb K^{18q+9}. \tag{RQ5}
\]

The new-pole and axis groups alone have at most 15q+9 rows. On the
18q boundary coefficient space they leave at least 3q−9 directions for
q>=4. Hence the matching conditions RQ4, or equivalent information, are
essential to this sufficient ambient-quotient approach. This is not a
dependence result for the raw sources.

## Eighteen columns associated with one old block

Fix any old t. For every q>=2 the eighteen actual columns

\[
 \{\widehat Q_{N,t,a,b}:a,b=0,1,2\}\ \cup\
 \{\widehat Q_{t,N,a,b}:a,b=0,1,2\} \tag{RQ6}
\]

are generically independent modulo Wwide_q K_N. In fact stripped new-line
residues already separate them.

For a nonvanishing witness coalesce the old matrices to H=K(A), and put
r=q−1. On a new line L_Nc=0 set v=A_N(c,:)diag(X), so v1=0. Only
six of RQ6's columns contribute there. Write their outgoing coefficients
alpha_b and incoming coefficients beta_i, and put
ell=sum_i beta_i A(i,c)X_i/L_i. After removing the common X_c factor,
their residue before stripping is

\[
 (v\operatorname{diag}(\alpha)H+\ell v)H^r. \tag{RQ7}
\]

The left kernel of K_N^−1 on this line is span(v). Consequently no
stripped new pole means
\[
 v\operatorname{diag}(\alpha)H+\ell v=\lambda vH^{-r}.
\]
Taking row sums forces all alpha_b to equal one scalar kappa, because
sum_b alpha_b A_N(c,b)X_b vanishes identically on L_Nc.

On the two-dimensional zero-sum space set tau=tr(H)−1 and delta=det(H).
Define S0=0,S1=1,S_(j+1)=tau S_j−delta S_(j−1). Cayley–Hamilton gives

\[
 H^{-r}=\frac{-S_rH+S_{r+1}I}{\delta^r}
 \quad\hbox{on the zero-sum space}. \tag{RQ8}
\]

Generically v and vH are independent. If kappa!=0, comparison in that
basis implies

\[
 \ell/\kappa=-S_{r+1}/S_r=-\tau+\delta S_{r-1}/S_r. \tag{RQ9}
\]

At each of the three old-line intersections, tau has a nonzero simple
pole and delta has at most a simple pole. The recurrence shows S_r has
leading pole tau^(r−1); therefore delta S_(r−1)/S_r is regular there
(and is zero when r=1). Matching the three principal parts in RQ9
forces the particular function ell/kappa to be

\[
 -\sum_i A(i,i)X_i/L_i=-\operatorname{tr}H=-\tau-1. \tag{RQ10}
\]

There is no arbitrary constant in this step: each of the three Xi/Li has
its own nonzero pole, so its coefficient is fixed by that pole. RQ9–RQ10
would give delta S_(r−1)/S_r=−1. At an ordinary coordinate-axis point
on the new line, delta=0 and tau!=0, hence S_r=tau^(r−1)!=0. The
identity would read 0=−1. Thus kappa=0; comparing the H coefficient
in RQ8 then gives lambda=0, followed by ell=0 and all beta_i=0.
The three c sectors use disjoint coefficients, proving independence.

## A common positive witness and the collision limit

Use G with rows (1,2,7),(1,5,3),(1,11,13), old time factors (1,1),
and new factors (2,3). Its determinant is 54. The new line coefficients
(n1,n2) are (4,21),(10,9),(22,39). They avoid every old line and
coordinate-axis collision. Evaluating those new lines at the three old
pair nodes gives, up to nonzero representative scaling, the triples
(50,38,176), (38,−10,56), and (59,−7,23); none vanish.

At X2=0, X1=1, X0=−n1, all old denominators are nonzero and
tau=−3n1/((2−n1)(5−n1)) is nonzero. This supplies RQ10's contradiction.
At X1=X2=1, X0=−n1−n2, the scalar n2(vH)_1−n1(vH)_2 is nonzero
for all three sectors. For c=0 it is less than −3732; for c=1 it equals
−18506/110; for c=2 it is less than −214. These verified rational
calculations establish the required v,vH independence. The witness
conditions do not depend on r.

The old nodes coincide at this witness. Do not substitute it into the
9q node-coordinate matrix. Instead take finite ordinary-point evaluations
of the stripped new-line residue functions, avoiding the old poles and
coordinate axes. Their proved functional independence supplies a nonzero
evaluation minor. Its entries are regular in nearby old time factors,
so that minor stays nonzero after the old times split. At every split
fixture these residue evaluations annihilate the appended ambient, proving
the generic RQ6 statement with valid distinct-line geometry.

The unresolved sufficient induction condition is full rank 18q of T_N
on all 18q boundary columns. The uniform rank-18 subfamily does not give
that condition, and ranks from overlapping tests cannot simply be added.

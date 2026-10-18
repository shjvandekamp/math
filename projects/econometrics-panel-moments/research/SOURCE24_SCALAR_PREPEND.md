# Scalar ordered-deletion independence by prepending

**Status: independently audited paper proof with an external exact base
certificate. Not yet a Lean independence theorem.**

The [scalar investigation](https://chatgpt.com/c/6ad1967a-b348-83ed-b108-5f0580589d92)
provided a prepend induction that closes the scalar gap in (LC37).
The primary researcher reconstructed the base from integer polynomial
kernels; independent local reviews checked the induction, axis formulas,
coefficient determinant, and parameter normalization. The result concerns
the scalar deletion family used in the collision argument, not the full
equation-(24) source family.

## Statement and a fixed positive common matrix

Let v=A_*(c,:)diag(X), restrict to L_*c=0, and let
T_t=K_1...K_(t-1)K_(t+1)...K_m in increasing order.
For every m>=3 and output e, the 3m functions
(X_a/L_ta)(v T_t)_e, together with the full-product scalar
(v K_1...K_m)_e, are generically independent over coefficients constant
in X. The genericity concerns the common-G parameter family with
independent time factors. Multiplication by one common nonzero rational
function of X preserves this independence.

It suffices to give a specialization with one fixed positive matrix:

\[
 \widetilde G=I+\mathbf1\mathbf1^T
 =\begin{pmatrix}2&1&1\\1&2&1\\1&1&2\end{pmatrix},
 \qquad
 G_0=\begin{pmatrix}1&1/2&1/2\\1&2&1\\1&1&2\end{pmatrix}.
 \tag{SP1}
\]

Row scaling changes no kernel. Use G0 for the model and compute earlier
row forms with Gtilde; this only rescales the state-zero deletion columns.
For terminal state c=0 choose (u_*,v_*)=(2,2), giving v=X and the line
X_0+X_1+X_2=0. Initially take e=1 and divide every function by X_1:

\[
 \phi_{ta}=\frac{X_a}{L_{ta}}\frac{(XT_t)_1}{X_1},\qquad
 \beta_m=\frac{(XQ_m)_1}{X_1},\qquad Q_m=K_1\cdots K_m.
 \tag{SP2}
\]

The output division is canceled using the last kernel; for m>=3 all
deletion products are nonempty. The induction proves independence of
the augmented 3m+1 functions, not just the deletion functions.

## The preserving prepend and its three new directions

Prepend a new block with (u,v)=(1+epsilon,1+2epsilon). Write
D=diag(0,1,2) and ell=X_1+2X_2. On the terminal line,

\[
 L_{{\rm pre},a}=X_a+\varepsilon(\ell+D_{aa}X_a),\qquad
 K^\circ=I+
 \begin{pmatrix}1/X_0\\1/X_1\\1/X_2\end{pmatrix}X,\qquad
 XK^\circ=4X.
 \tag{SP3}
\]

This limit is not an identity kernel. It preserves the actual starting
row, so every inherited deletion function tends to 4 phi_ta with the
correct order: its product is X K_pre T_t. The three columns deleting
the new block and the new full-product column are

\[
 C_a(\varepsilon)=\frac{X_a}{L_{{\rm pre},a}}\beta_m,\qquad
 Z(\varepsilon)=\frac{(XK_{\rm pre}Q_m)_1}{X_1}.
 \tag{SP4}
\]

At zero, C_a=beta_m and Z=4 beta_m. Retain C_0 and replace the
other three columns by (C_1-C_0)/epsilon, (C_2-C_0)/epsilon,
(Z-4C_0)/epsilon. These are permitted parameter-only column operations.
Direct differentiation gives

\[
 X\dot K=r-\ell\left(\sum_a1/X_a\right)X,\qquad
 r=3XD-3X-\ell\mathbf1^T,
\]
\[
 \begin{split}
 \Psi_1&=(-1+\ell/X_0-\ell/X_1)\beta_m,\\
 \Psi_2&=(-2+\ell/X_0-\ell/X_2)\beta_m,\\
 \Psi_3&=(rQ_m)_1/X_1+
                  \ell(3/X_0-1/X_1-1/X_2)\beta_m .
 \end{split}
 \tag{SP5}
\]

Use binary coordinates X=(-s-t,s,t) and the three axis representatives
P_0=(0,1,-1), P_1=(-1,0,1), P_2=(-1,1,0). Old row forms are
generically units at all three points. The old augmented functions
are regular there, as is (rQ_m)_1/X_1 because the last old kernel
supplies X_1. Also ell(P_a) is nonzero. The three principal-part
observations [X_a F/ell] at P_a annihilate all inherited columns
and give

\[
 \operatorname{diag}(\beta_m(P_0),\beta_m(P_1),\beta_m(P_2))
 \begin{pmatrix}1&1&3\\-1&0&-1\\0&-1&-1\end{pmatrix}.
 \tag{SP6}
\]

The numerical determinant is one. If the three endpoint values are
nonzero, these supply three pivots modulo the whole old augmented
span. The induction hypothesis then handles the pole-free inherited
part. This resolves the gap that cancellation of new poles alone
left in (LC37); the new block is prepended, not appended.

## Endpoint factors and a concrete coefficient recurrence

Put Delta_t=product_a L_ta, B_t=Delta_t K_t, and
R_m=product_t Delta_t. The cleared functions
p_ta=R_m phi_ta and U_m=R_m beta_m are homogeneous binary forms
of degree 3m. The actual ordered formulas are

\[
 p_{ta}=
 \frac{XB_1\cdots\widehat B_t\cdots B_m e_1}{X_1}
           X_a\prod_{b\ne a}L_{tb},\qquad
 U_m=\frac{XB_1\cdots B_m e_1}{X_1}.
 \tag{SP7}
\]

In the chart s=1,t=z, let D_m be their coefficient determinant:
rows z^0 through z^(3m), columns (t,a) in lexicographic order,
then U_m. The endpoint values are exactly

\[
 \begin{split}
 U_m(P_0)&=\prod_{t=1}^m[-3u_tv_t(u_t-v_t)],\\
 U_m(P_2)&=\prod_{t=1}^m[-3u_t(u_t-1)],\\
 U_m(P_1)&=-u_m(v_m^2-1)
                    \prod_{t<m}[-3v_t(v_t-1)].
 \end{split}
 \tag{SP8}
\]

At X_a=0, the other two coordinates i,j satisfy X_i=-X_j.
The zero-sum row supported on them is multiplied by the active
binary determinant 3 d_ti d_tj X_i X_j/(L_ti L_tj).
For P_0,P_2 this immediately gives (SP8). At P_1, cancel the final
output X_1 first: the last factor becomes
u_m(X_0/L_m0+X_2/L_m2), after the preceding binary determinants.
This yields the third formula and retains the distinguished final
time. Every endpoint factor and every axis denominator condition is
a nonzero polynomial condition in the positive time parameters.

The induction also gives the exact determinant recurrence

\[
 D_{m+1}(\varepsilon)
 =2\,4^{3m}D_m
      U_m(P_0)U_m(P_1)U_m(P_2)\varepsilon^3
          +O(\varepsilon^4).
 \tag{SP9}
\]

For its normalization, Delta_pre(0)=delta=X_0X_1X_2.
The inherited polynomial columns are 4 delta p_ta and the retained
C_0 column is delta U_m. Their span is delta times the full
degree-3m binary space. Evaluation at the three axis representatives
detects its three-dimensional quotient in degree 3m+3.
The three derivative row factors are U_m(P_0), -2U_m(P_1),
-U_m(P_2), multiplied by the numerical matrix in (SP6).
The coefficient-to-axis quotient determinant contributes (-1)^(3m);
reordering the columns from (C_0,C_1,C_2,old,Z) contributes the
same sign. Their product is positive, giving exactly the factor two
in (SP9). The 3m inherited columns contribute 4^(3m).

## Exact base and the all-length conclusion

Take m=3 and earlier time factors (3,4),(4,3),(5,9).
The locally written verifier
`exploration/source24_scalar_prepend_certificate.py` constructs
the integer polynomials in (SP7) directly from the actual B matrices.
The 10-by-10 coefficient matrix modulo 17 has no-swap Gaussian pivots

\[
 (7,11,3,3,16,12,11,16,14,3),\qquad D_3\equiv9\pmod{17}.
 \tag{SP10}
\]

It also reconstructs the exact integer endpoint values

\[
 (U_3(P_0),U_3(P_1),U_3(P_2))
       =(-699840,-259200,-38880).
 \tag{SP11}
\]

The saved result contains all integer column coefficients, the modular
matrix and pivots. Independently building the actual first-order
prepended polynomial products gives order-three determinant coefficient
13 modulo 17, agreeing with (SP9). This latter check supports the
formula; the arbitrary-length proof is the residue/quotient argument
above, not extrapolation from the two sizes.

Since D_m and the endpoint/denominator conditions are nonzero
polynomials for the same fixed Gtilde, their nonempty generic opens
intersect in the positive old-time domain. Equation (SP9) then gives
a nonzero D_(m+1) for sufficiently small positive epsilon. Starting
from (SP10) proves augmented independence for every m>=3.

There is an explicit iterated valuation. Put r=m-3 and retain the
last three base blocks. List the r prepended blocks in their final
left-to-right order, with parameters epsilon_1,...,epsilon_r.
Extract the lowest epsilon_1 power first, then epsilon_2, and so on.
With A=U_3(P_0)U_3(P_1)U_3(P_2), the result is

\[
 D_3(2A)^r4^{3r(r+5)/2}54^{r(r-1)/2}
       \varepsilon_1^3\varepsilon_2^6\cdots
       \varepsilon_r^{3r}\ne0.
 \tag{SP12}
\]

The factor 54 comes from the three new endpoint factors
(3epsilon,-6epsilon,-3epsilon). The ordering is newest-prepend to
oldest-prepend; chronological prepend order reverses the displayed
exponents. This is an iterated coefficient statement, not a claim
about simultaneous total-degree leading terms.

Finally, state permutations preserve Gtilde. Normalizing time factors
back to first coordinate one only rescales parameters and columns.
The other terminal states yield v=X with factors (1/2,1) for c=1
and (1,1/2) for c=2. Thus the theorem holds for every terminal state
and output coordinate: after permuting the output, rechoose the
terminal row and its factors to realize v=X again. This also covers
output equal to terminal state, beyond simultaneous permutations of
the initial distinct pair (c,e)=(0,1). Diagonal rescaling of X can send the
terminal factors to any prescribed positive values while inversely
rescaling the earlier factors. A nonzero specialization proves that
the corresponding generic common-G determinant is not the zero
polynomial.

The base and first-coefficient evidence are in
`exploration/source24-scalar-prepend-certificate-results.json`.
The paper theorem and these finite certificates have not yet been
formalized as an arbitrary-m Lean rank theorem.

## Polynomial observations and every fixed perturbation direction

There is a stronger version that needs no finite base. Keep Gtilde and
the line sum X_a=0. Let l(X) be a polynomial column, independent of
the earlier time parameters, and define

\[
 f_{ta}=\frac{X_a}{L_{ta}}XT_t l(X),\qquad
 b_m=XQ_m l(X),\qquad b_0=Xl(X).
 \tag{SP13}
\]

If b_0(P_a) is nonzero for each of the three axis representatives,
the augmented 3m+1 functions in (SP13) are generically independent
for every m>=0. Here no coordinate output is divided out.

To prove this, prepend the same block (SP3). The inherited columns
tend to 4 f_ta. Retain the new full-product column Z, with Z(0)=4b_m,
and replace the three new deletion columns by (C_a-Z/4)/epsilon.
All their numerators vanish at epsilon=0. The regular part rQ_m l
has no axis poles even at m=0. The three principal-part observations
of their first coefficients give

\[
 \operatorname{diag}(b_m(P_0),b_m(P_1),b_m(P_2))
       \left(-I+\tfrac14\mathbf1\mathbf1^T\right),
 \qquad
 \det\left(-I+\tfrac14\mathbf1\mathbf1^T\right)=-\tfrac14.
 \tag{SP14}
\]

They annihilate every inherited column and the retained b_m. On an
axis, the row X is supported on the other two states and has sum zero.
Thus XQ_m=(product_t lambda_t)X there, where lambda_t is the nonzero
active binary determinant used in (SP8). Consequently
b_m(P_a)=(product_t lambda_t(P_a))b_0(P_a) is generically nonzero.
The old independence and these three new pivots prove the induction,
starting from the single nonzero polynomial b_0. The specialization
and residue argument is over the parameter rational-function field;
nonzero minors then give nonempty positive parameter opens.

This applies directly to the actual transverse observation (LC33).
Fix a real perturbation direction with three distinct weights
(0,tau,nu). At G0, terminal state c=0 and terminal factors (2,2),
let H=G0 diag(0,tau,nu) G0^(-1). Then

\[
 H_{01}=(3\tau-\nu)/8,\qquad H_{02}=(3\nu-\tau)/8,
 \qquad l=H_{02}L_2e_1-H_{01}L_1e_2,
\]
\[
 (b_0(P_0),b_0(P_1),b_0(P_2))
       =(\tau-\nu,-H_{01},H_{02}).
 \tag{SP15}
\]

The earlier forms may still be computed with Gtilde: row normalization
only gives nonzero parameter-only deletion-column factors. The terminal
forms and H in (SP15) use the actual normalized G0. If both H entries
are nonzero, (SP13)--(SP14) prove augmented independence from m=0.
If one vanishes, the observation is a common nonzero linear factor
times one coordinate-output family, so (SP1)--(SP12) supply augmented
independence for m>=3. They cannot both vanish for the prescribed
distinct weights. This covers every such fixed real direction.
The artificial direction (1,2) used to prepend earlier time factors
is independent of the fixed direction perturbing the final block.

Permute states to send any terminal state c to zero, and subtract the
new zeroth perturbation weight as in (LC34). The three weights remain
distinct. Invert the birational normalization to obtain a nonzero
minor for that sector in the original common-G/time parameter space.
The three sector witnesses may have different terminal time factors;
intersect their nonzero-minor opens in the common irreducible parameter
space, rather than asserting that one terminal specialization handles
all sectors. This intersection also meets the positive domain.

Therefore, for every fixed real distinct-rate direction and m>=3,
the actual three uncorrected incoming observation blocks have total
generic rank 9m. Their column supports are disjoint. This conclusion
is still before quotienting by the leading source family and the
twelve local jets. The resulting corrected rank bound, with that
loss retained, is recorded in (LC47). In fact the augmented columns
are realized by three actual sums of shared jets, as proved in
(LC48)--(LC50), giving a further three pivots. They are not counted
as independent artificial source columns.

Two independent local reviewers checked the polynomial base, the
principal-part determinant, the exceptional directions, and the
intersection of the three sector opens. These are audited paper
theorems, not yet arbitrary-length Lean independence theorems.

## Three individual shared columns fill the transverse target

The preceding argument extends to the three individual shared columns,
not only their sum. This yields the full 3m+3-dimensional observation
space in each sector. The proof below is independently audited and
uses a three-quadratic auxiliary base, with no finite base certificate.

Replace the fixed common matrix by the positive family

\[
 \widetilde G_r=\operatorname{diag}(r_0,r_1,r_2)+\mathbf1\mathbf1^T,
 \quad r_a>0,\quad w_a=1/r_a,\quad S=1+\sum_a w_a.
 \tag{SP16}
\]

Normalize its first column by row scaling and, for terminal state zero,
choose terminal factors (r_0+1,r_0+1). The actual terminal row is
(1,1,1), so v=X on sum X_a=0. Let A be this terminal table, B=A^(-1),
H=A diag(0,tau,nu) A^(-1), h=H_01, k=H_02. Write L=L_q,
eta=dot L_0=hL_1+kL_2 on the line, and
l=hL_1 e_0+eta e_1. Define the scalar functions

\[
 f_{ta}=\frac{X_a}{L_{ta}}XT_t l,\qquad
 g_b=X_b(e_bQ_m l)-\eta L_1 B_{b1},\qquad
 \beta_m=XQ_m l=\sum_b g_b.
 \tag{SP17}
\]

Earlier forms are computed with Gtilde_r; normalization only rescales
the deletion columns. For m>=1 these f columns are the actual incoming
observations after their nonzero transition factors and common X_0
factor are removed. The three g columns are exactly the observations
of the three individual actual U_(1,0,b), divided by X_0, since the
terminal row entries are one. P_1=Q_m is the actual increasing word.

At m=0, Q_0=I. The three g columns are auxiliary quadratics, not
additional source columns at a zero-length horizon. On L_0=0 they are

\[
 g_0=\kappa L_1L_2,\qquad
 g_1=B_{12}(hL_1+kL_2)L_2,\qquad
 g_2=-B_{21}(hL_1+kL_2)L_1,
\]
\[
 \kappa=hB_{02}-kB_{01}=\frac{\nu-\tau}{\det A}.
 \tag{SP18}
\]

In the basis (L_1^2,L_1L_2,L_2^2), their determinant is
-kappa B_12 B_21 h k. It is generically nonzero for every fixed
distinct-rate direction. More explicitly,

\[
 h=\frac{w_1[\tau(1+w_0)+(\tau-\nu)w_2]}{(r_0+1)S},\qquad
 k=\frac{w_2[\nu(1+w_0)+(\nu-\tau)w_1]}{(r_0+1)S},
 \quad B_{12}=B_{21}=-\frac{w_1w_2}{(r_0+1)S}.
 \tag{SP19}
\]

For example, sufficiently large positive r_a make h and k nonzero,
because tau and nu are nonzero. Also nu-tau is nonzero. At the three
axis representatives from (SP6),

\[
 (\beta_0(P_0),\beta_0(P_1),\beta_0(P_2))
       =(\tau-\nu,-r_0h,r_0k).
 \tag{SP20}
\]

These endpoint values propagate through each earlier kernel by its
active binary determinant, as in the proof of (SP14).

Prepend an earlier time with factors (1+epsilon,1+2epsilon). Put
D=diag(0,1,2) and ell=X_1+2X_2; this artificial direction is again
independent of the prescribed terminal perturbation. At epsilon=0,

\[
 K^\circ=I+\begin{pmatrix}w_0/X_0\\w_1/X_1\\w_2/X_2\end{pmatrix}X,
 \qquad XK^\circ=SX.
 \tag{SP21}
\]

The inherited f columns tend to S f. The new g vector tends to
g+w beta, so its change-of-basis matrix is I+w 1^T, with determinant
S. Retain those three columns. Scale each new deletion column by r_a,
calling the result C_a; then C_a(0)=beta_m. The new full-product scalar
beta_new=sum_b g_(b,new) tends to S beta_m. Thus all three
C_a-beta_new/S vanish at epsilon=0.

For completeness, the actual derivative identity is
X dot K=(S-1)XD-(sum_a w_a D_aa)X-ell w^T
-ell(sum_a w_a^2/X_a)X. Its first three terms are regular at the
axis points after multiplication by the old polynomial observation.
Dividing the three vanishing column combinations by epsilon and taking
the principal parts [X_i F/ell] at P_i gives

\[
 \operatorname{diag}(-w_i\beta_m(P_i))
                   (I-w\mathbf1^T/S),\qquad
 \det(I-w\mathbf1^T/S)=1/S.
 \tag{SP22}
\]

All inherited limiting columns are regular at these points. The endpoint
values and ell(P_i) are nonzero, so (SP22) supplies three independent
new directions modulo the inherited span. Its pole-free part is handled
by the induction hypothesis and the invertible inherited change above.
Starting from (SP18) proves independence of all 3m f columns and all
three g columns for every m>=1. At each step the old nonzero-minor,
endpoint and row-form conditions intersect in the same positive-time
domain for the fixed selected Gtilde_r. Small positive epsilon then
provides the next witness.

Permuting states and intersecting their nonzero-minor opens proves the
simultaneous statement in the unrestricted common-G parameter family:
for every fixed real direction with three distinct rates, the actual
9m incoming columns and the nine individual shared columns with s=1
have normalized transverse observation rank 9m+9. The binary degree
bound in (LC52) shows that this is the full target. The resulting
conditional source-rank bound and exact remaining 9q-column problem
are stated in (LC53)--(LC54). Full source independence is still open.

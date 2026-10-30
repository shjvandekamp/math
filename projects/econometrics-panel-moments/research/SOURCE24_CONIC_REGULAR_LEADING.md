# Conic regular block: analytic cancellation and its leading operator

**Status: independently audited paper results; not Lean formalized.**
The analytic cancellation and leading-operator statements below were
proposed in the [Pro15 investigation](https://chatgpt.com/c/6ad14ae9-5a94-83eb-a1f3-0fa76fa51155)
and checked independently by the local researchers. They retain both
the outgoing correction and the old-block correction. Nonvanishing of
the resulting determinant for all lengths remains open. The final section
records an independently reconstructed exact finite certificate at n=5.

Use the conventions of [the conic transverse reduction](SOURCE24_CONIC_TRANSVERSE.md)
and its [even-length first-jet proof](SOURCE24_CONIC_EVEN_JET.md).
There are n old blocks, with n at least 2, and one new block N. Put

\[
 G_\alpha=(\alpha_a^b)_{a,b=0}^2,\qquad
 A_t=G_\alpha\operatorname{diag}(1,b_t,b_t^2),\qquad
 r_{ta}=\alpha_a b_t,\qquad
 L_{ta}=X_0+r_{ta}X_1+r_{ta}^2X_2.
 \tag{CR1}
\]

The positive parameters \(\alpha_0,\alpha_1,\alpha_2\) are distinct,
all old \(r_{ta}\) are distinct, and the new time is \(b_N=\epsilon\).
Write \(x_c=\alpha_c\epsilon\). For sufficiently small positive
\(\epsilon\), the old and new nodes have the usual nonincident conic
geometry. The limiting geometry at \(\epsilon=0\) is used only through
the analytic extensions proved below.

Let \(P_s\) be the product of all old kernels with block s first and
the other old blocks in increasing order. Let \(P^{\widehat t}\)
be the increasing old product with block t omitted. Thus their lengths
are n and n minus 1, respectively, and both are nonempty. The actual
incoming and normalized outgoing rows in new sector c are

\[
 \begin{split}
 F^{\rm in}_{t,A,c}
 &=\frac{X_A r_{tA}^{\,c}X_c}{L_{tA}}
       e_c(I-K_NP^{\widehat t}),\\
 \overline F^{\rm out}_{s,c,j}
 &=\frac{F_{N,s,c,j}}{x_c^j}
   =\frac{X_cX_j}{L_{Nc}}e_j(I-P_s).
 \end{split} \tag{CR2}
\]

All rows are homogeneous of degree one and have row sum zero.
The normalized outgoing columns in every block below are exactly those
in (CR2).

## Analytic outgoing elimination

On the new line of sector c use

\[
 X=(xy,-x-y,1),\qquad x=x_c,\qquad
 v_x=(xy,-x(x+y),x^2),\qquad h_x=(x,0,-y).
 \tag{CR3}
\]

The old node of line i is at \(y=r_i\), independently of x. The
transverse functional is contraction with \(h_x\), which annihilates
\(v_x\). In the ordinary-y residue convention define \(M_n(x)\)
from the functions

\[
 g_{s0}=y e_0P_sh_x,\qquad
 g_{s1}=-(x+y)e_1P_sh_x,\qquad
 g_{s2}=e_2P_sh_x.
 \tag{CR4}
\]

With state-zero columns first, the normalized outgoing transverse block
has the factorization

\[
 \overline P_c=M_n(x)\operatorname{diag}(xI_n,I_{2n}),\qquad
 Q_c=xq_1+O(x^2),\qquad
 M_n(0)=\begin{pmatrix}D&0\\B&T\end{pmatrix}.
 \tag{CR5}
\]

The common sign between the source transverse residues and the residues
in (CR4) is included in the transverse row convention for both
\(\overline P_c\) and \(Q_c\). Common nonzero transverse row scalings
leave \(\Lambda_c=\overline P_c^{-1}Q_c\) unchanged.

The n state-zero rows of the leading matrix have diagonal pivots

\[
 D_{tt}=r_{t0}^{\,3}\prod_{j\ne t}d_j(r_{t0}),\qquad
 d_j(y)=\frac{y(\alpha_1b_j-\alpha_2b_j)}
                  {(\alpha_1b_j-y)(\alpha_2b_j-y)}.
 \tag{CR6}
\]

They are nonzero under the displayed geometry. Indeed, at x equal to
zero a state-zero pole can occur only in the first old block of the
word. At that pole
\(\operatorname{Res}_{y=r_{t0}}e_0K_t=(0,r_{t0},-r_{t0})\).
The binary tail multiplies this zero-sum row by the product of its
determinants \(d_j(r_{t0})\). Contraction with \(h_0\), followed by
the outer y in \(g_{s0}\), gives the remaining two factors of
\(r_{t0}\).

For odd n the established binary theorem makes T invertible. For even
n it has nullity two. Write the analytic blocks of M as
\(D(x),A(x),B(x),T(x)\), with \(A(0)=0\), and set

\[
 \Sigma(x)=T(x)-B(x)D(x)^{-1}A(x),\qquad
 J=L\Sigma'(0)U,
 \tag{CR7}
\]

where U spans the right kernel of T and L its left kernel. In even
parity assume \(J\) is invertible. The even first-jet theorem proves
that this is a generic conic condition for each even n. It is an
additional hypothesis at an individual parameter choice; distinct
\(\alpha_a\) alone does not imply it.

Under these hypotheses \(\Lambda_c\) is analytic at x equal to zero
in both parities. In even parity,
\(\Sigma^{-1}=x^{-1}UJ^{-1}L+O(1)\), and the pole of \(M^{-1}\)
has image in \(\ker M(0)=\{0\}\oplus\operatorname{im}U\).
Its state-zero rows are therefore bounded. Multiplication by
\(Q_c=O(x)\) cancels the pole in the binary rows, and the extra
state-zero factor \(x^{-1}\) in (CR5) is cancelled by those bounded
rows times Q. More explicitly, partition \(q_1=(q_{1,0},q_{1,b})\)
and \(\Lambda_c=(\Lambda_{c,0},\Lambda_{c,b})\). Then in even parity

\[
 \begin{split}
 \Lambda_{c,b}(0)
   &=UJ^{-1}L(q_{1,b}-BD^{-1}q_{1,0}),\\
 \Lambda_{c,0}(0)
   &=D^{-1}\{q_{1,0}-A'(0)\Lambda_{c,b}(0)\}.
 \end{split} \tag{CR8}
\]

For odd \(n\ge3\), the constant has a simpler formula. Set
\(r(t)=\min(\{1,\ldots,n\}\setminus\{t\})\). Its only possibly
nonzero outgoing coordinate is
\[
 \Lambda_{c;(s,0),(t,A)}(0)
  =\mathbf1_{s=r(t)}\,r_{tA}^{\,c}
       \left.\frac{X_A}{L_{tA}d_t(y)}
       \right|_{X=(0,-y,1),\ y=r_{r(t),0}},
 \qquad
 \Lambda_{c;(s,1),(t,A)}(0)
 =\Lambda_{c;(s,2),(t,A)}(0)=0.
 \tag{CR8a}
\]
Indeed, the normalized outgoing state-zero scalar starts with
\(-xy^2(P_s)_{02}\), and the incoming scalar starts with
\(-xy^2r_{tA}^{\,c}(X_A/L_{tA})
 [(P^{\widehat t})_{02}-(P^{\widehat t})_{12}]\).
Only the first block \(r(t)\) of the omitted word can contribute an
old state-zero pole. The binary tails of the full and omitted words
differ by the determinant \(d_t\), giving the positive ratio in
(CR8a). The binary leading matrix is invertible, so its constant
coordinates vanish. This formula and its sign were independently
checked in addition to the block analyticity argument.

Sector c equal to zero creates no additional singularity: its shared
factor \(X_c\) was removed in defining the transverse new-line
residue. If the incoming shared state A is zero, its additional
\(X_A=xy\) factor gives \(Q_c=O(x^2)\), and consequently
\(\Lambda_c=O(x)\) in either parity.

## Whole-line longitudinal residue and its two departure factors

For one incoming column let
\(G=F^{\rm in}-\sum_{s,j}\lambda_{sj}\overline F^{\rm out}_{s,c,j}\),
where \(\lambda\) is its column of \(\Lambda_c\). On \(L_{Nc}=0\),
its new-line residue divided by \(X_c\) is

\[
 r=-\frac{X_A r_{tA}^{\,c}}{L_{tA}}v_xP^{\widehat t}
      +\sum_{s,j}\lambda_{sj}X_je_jP_s
      -\sum_{s,j}\lambda_{sj}X_je_j.
 \tag{CR9}
\]

This row is homogeneous of degree one and zero-sum. Each component j
has a factor \(X_j\), and its only poles are the simple old nodes.
Transverse cancellation says that each old-node residue is parallel
to \(v_x\). These local conditions imply an exact whole-line identity,
including its polynomial part:

\[
 r=v_x f_c,
 \qquad
 \begin{split}
 f_c=\frac{r_0}{X_0}
 &=-\frac{X_A r_{tA}^{\,c}}{L_{tA}}
          \frac{v_xP^{\widehat t}e_0}{X_0}\\
 &\quad+\sum_{s,j}\lambda_{sj}X_j
          \frac{e_jP_se_0}{X_0}
       -\sum_s\lambda_{s0}.
 \end{split} \tag{CR10}
\]

To prove this without a choice of scalar principal parts, cancel the
final-column factor \(X_0\) in the nonempty products in (CR10).
The resulting f has only old poles and is homogeneous of degree zero.
At every old node it has the scalar residue needed to cancel r with
\(v_xf\). Their difference is therefore a homogeneous linear
polynomial row on the new line. It remains componentwise divisible by
\(X_j\), is zero-sum, and has component zero identically zero.
For x nonzero these properties force that polynomial row to vanish.
The formula after cancellation is analytic in x, so it also supplies
the extension at x equal to zero.

There is a second factor which this final-column cancellation does not
consume. For every old line \(i=(u,a)\),

\[
 \left. L_i f_c\right|_{L_i=0}=X_a\,\omega_{i,c},
 \tag{CR11}
\]

with a quotient regular at its matching point and analytic in x.
For a pole inside a product, arrival at state a supplies \(X_a\).
If it is the first block, the input row \(X_je_j\) or \(v_x\)
already supplies this factor. If it is the last block, its final
transition supplies the separate \(X_0\) removed in (CR10).
At the shared incoming pole the factor \(X_A\) is explicit. Thus,
also when a is zero, there are separate arrival and final-coordinate
factors; dividing by the final \(X_0\) does not remove the required
arrival factor.

Let W be the longitudinal block after outgoing elimination, in the
coefficient of \(v_{x_c}\) at the old/new node. With

\[
 P_{i,c}=(r_i\alpha_c\epsilon,-r_i-\alpha_c\epsilon,1),
\]

equations (CR9)--(CR11) give

\[
 W_{(i,c),\ell}
   =X_a(P_{i,c})X_c(P_{i,c})\,
       \omega_{(i,c),\ell}(\epsilon),
 \qquad \omega\text{ analytic at }\epsilon=0.
 \tag{CR12}
\]

Both factors are retained, including when a or c equals zero.

## The leading regular operator with the old correction retained

Let \(d_n=9n(n-1)\). The old pair-residue matrix \(O_n\) has
\(d_n\) columns and rows. Use the first two components of the raw
zero-sum row at every old cross-block node

\[
 P_{ij}=(r_ir_j,-r_i-r_j,1).
\]

Assume \(O_n\) is invertible. This assumption is essential: the
singular conic \(O_3\) must not be inverted or substituted into the
following formula. The bordered singular-block reduction in the
conic transverse note is a separate statement.

With old columns, normalized outgoing columns and incoming columns,
and old, transverse and longitudinal residue rows, write the full
matrix as

\[
 \begin{pmatrix}
 A&\overline B&E\\
 0&\overline P&Q\\
 C&\overline R&S
 \end{pmatrix},\qquad
 \Lambda=\overline P^{-1}Q,\qquad
 Z=E-\overline B\Lambda,\qquad
 W=S-\overline R\Lambda.
 \tag{CR13}
\]

Here A has size \(d_n\) and \(\overline P\) has size \(9n\).
The remaining regular Schur block is
\(H_n=W-CA^{-1}Z\), of size \(9n\). In particular, replacing Z
by E would discard the outgoing correction.

Define \(Z_0\) by taking old double residues of the following limiting
rational rows, with \(\Lambda_0=\Lambda(0)\):

\[
 \begin{split}
 E^{\rm row}_{0;t,A,c}
 &=\frac{X_A r_{tA}^{\,c}X_c}{L_{tA}}
                 (e_c-e_0P^{\widehat t}),\\
 \overline B^{\rm row}_{0;s,c,j}
 &=\frac{X_cX_j}{X_0}e_j(I-P_s),\\
 Z_0&=\rho_{\rm old}
        (E^{\rm row}_0-\overline B^{\rm row}_0\Lambda_0).
 \end{split} \tag{CR14}
\]

The old nodes have \(X_0\ne0\), so these limits and old residues
commute. Formula (CR14) is the matrix limit of Z in the raw old
coordinates; it is not a replacement by an auxiliary source family.

For an old source column \(\ell=(t,s,A,B)\), let its raw completed
row be

\[
 \widehat Q_\ell
 =\frac{X_A A_t(A,B)X_B}{L_{tA}}
       e_B P_s^{\widehat t},\qquad
 F_\ell=\frac{X_A A_t(A,B)X_B}{L_{tA}}e_B-\widehat Q_\ell.
\]

The word \(P_s^{\widehat t}\) has s first, omits t, and orders the
other old blocks increasingly. Define the \(9n\)-by-\(d_n\) matrix

\[
 U_n[(i,c),\ell]
 =\left.
    \frac{(\operatorname{Res}_{L_i}\widehat Q_\ell)_c}
         {X_aX_c}
   \right|_{X=(0,-r_i,1)},\qquad i=(u,a).
 \tag{CR15}
\]

The two factors are cancelled before evaluation. The same path argument
as for (CR11) proves regularity, including \(a=c=0\). Appending the
new kernel to an old source gives prefix minus
\(\widehat Q_\ell K_N\). Its longitudinal old/new residue therefore
has a minus sign, and

\[
 \frac{C_{(i,c),\ell}}{X_a(P_{i,c})X_c(P_{i,c})}
       =-U_n[(i,c),\ell]+O(\epsilon).
 \tag{CR16}
\]

Put \(\ell_2=e_2G_\alpha^{-1}\). The leading inverse kernel at a
fixed old node is

\[
 K_N^{-1}
 =\epsilon^{-2}\frac{X_0}{X_2}\,e_2^{\rm col}\ell_2
        +O(\epsilon^{-1}).
 \tag{CR17}
\]

The row \(\ell_2\) is zero-sum because the first column of
\(G_\alpha\) is the all-ones column. Define \(D_n\), of size
\(d_n\), separately at each old node by

\[
 (z_0,z_1)\longmapsto
       r_ir_j z_2\bigl((\ell_2)_0,(\ell_2)_1\bigr),
 \qquad z_2=-z_0-z_1.
 \tag{CR18}
\]

Thus \(D_n\) is the coefficient of \(\epsilon^{-2}\) in the
inverse node transport. Since the appended old columns have old
residues equal to their old residues multiplied by \(K_N(P_{ij})\),

\[
 A=K_{\rm node}O_n,\qquad
 A^{-1}=O_n^{-1}K_{\rm node}^{-1},\qquad
 \epsilon^2K_{\rm node}^{-1}=D_n+O(\epsilon).
 \tag{CR19}
\]

The notation \(K_{\rm node}\) denotes this linear transport in the
first-two raw coordinates, not an additional common source matrix.

Finally let \(S_\epsilon\) be diagonal on the longitudinal rows:

\[
 (S_\epsilon)_{(i,c),(i,c)}
       =\frac{\epsilon^2}{X_a(P_{i,c})X_c(P_{i,c})}.
 \tag{CR20}
\]

Combining (CR12), (CR14), (CR16) and (CR19) proves the leading theorem

\[
 \boxed{\quad
 S_\epsilon W=O(\epsilon^2),\qquad
 S_\epsilon H_n
    =U_nO_n^{-1}D_nZ_0+O(\epsilon).
 \quad} \tag{CR21}
\]

The positive sign of the leading old correction comes from
\(H_n=W-CA^{-1}Z\) and the negative sign in (CR16).
The old inverse and the outgoing correction both remain in (CR21).

For each old time t, direct multiplication of the nine departure/final
factor pairs gives

\[
 \prod_{a,c=0}^2X_a(P_{ta,c})X_c(P_{ta,c})
 =\epsilon^6\alpha_0^9\alpha_1^6\alpha_2^3b_t^{12}
           (1+O(\epsilon)).
\]

Therefore, with
\(\kappa_n=(\alpha_0^9\alpha_1^6\alpha_2^3)^n
\prod_{t=1}^n b_t^{12}\),

\[
 \boxed{\quad
 \lim_{\epsilon\to0}\epsilon^{12n}\det H_n
       =\kappa_n\det(U_nO_n^{-1}D_nZ_0).
 \quad} \tag{CR22}
\]

This identity also holds when its right side is zero. It is a leading
operator reduction, not a nonvanishing theorem. Generic invertibility
of \(O_n\) within the conic specialization and nonvanishing of the
last determinant for all admissible lengths are not proved here.

## Exact five-to-six-block witness

The local implementation
[`source24_conic_regular_leading.py`](../exploration/source24_conic_regular_leading.py)
reconstructs (CR21) from the actual ordered words, without using the
external investigation's code. Its
[exact output](../exploration/source24-conic-regular-leading-results.json)
uses n=5, alpha=(1,2,3), old times (1,5,25,125,625), and prime 1000003.

| Quantity | Size | Value modulo 1000003 |
| --- | ---: | ---: |
| det O_5 in the raw first-two-component coordinates | 180 | 969253 |
| det M_5(0) in ordinary-y residue coordinates | 15 | 155046 |
| det(U_5 O_5^{-1} D_5 Z_0) | 45 | 214966 |
| kappa_5 | — | 528352 |
| kappa_5 det(U_5 O_5^{-1} D_5 Z_0) | — | 375301 |

All inversions used in this reconstruction have nonzero denominators
modulo the prime. The nonzero values therefore certify nonzero rational
quantities at the displayed positive old parameters. The controls check
the conversion from cross-point coordinates to P=(r_i r_j,-r_i-r_j,1),
the actual incoming formula, and the exact equation O_5 Y=D_5 Z_0.
They also compare U against a separate regularization of the actual K
words, including both cancelled factors when a=c=0, and check M_5(0)
against an independent ordinary-y residue construction.

The run exited zero in 0.769 seconds with maximum RSS 22,298,624 bytes
and no cutoff. The implementation and its residue normalizations passed
an independent local audit. This is an external exact certificate, not
a Lean-checked determinant.

Together with (CR22) and the outgoing transverse theorem, this proves
that O_6 is nonsingular for the displayed old parameters and all
sufficiently small positive appended times epsilon. Thus generic conic
O_6 nonvanishing now has a witness. No particular nonzero epsilon has
been evaluated here, and no explicit threshold is asserted. This
consequence concerns the canonical pair-source matrix O_6; it does not
prove independence of the whole selected source family (24).

The remaining uniform task is to prove nonvanishing of
det(U_n O_n^{-1} D_n Z_0) for the required old lengths, or find another
leading term where it vanishes. The exceptional conic O_3 cannot be
inverted and still needs its separate singular-base treatment.

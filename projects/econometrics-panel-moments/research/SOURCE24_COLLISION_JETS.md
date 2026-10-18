# Collision jets retain two-way old-pair mixing

Audited research note, 16 October 2026. An isolated three-line collision
has a regular numerator-jet formulation. A reconstructed exact fixture
shows that the resulting retained-old Schur matrix has nonzero blocks
in both directions between two old pairs. Thus a simultaneous pair
ordering cannot make this particular corrected matrix triangular.
This is an obstruction to that proposed proof route, not to generic
source independence.

## The exact local observation change

Take three selected lines from distinct time blocks and use coordinates
\[
 x=L_{i,a},\qquad y=L_{j,b},\qquad
 \ell=\varepsilon+\alpha_\varepsilon x+\beta_\varepsilon y,
 \quad \alpha_0\beta_0\ne0.
 \tag{CJ1}
\]
Assume all other row lines are units at the limiting crossing. Every
actual source uses each time block at most once, so
\(f_R=xy\ell R\) is regular there. Componentwise, the three pair
observations are
\[
 r_{xy}=\frac{f_R(0,0,\varepsilon)}{\varepsilon},\quad
 r_{x\ell}=-\frac{\beta_\varepsilon}{\varepsilon}
       f_R(0,-\varepsilon/\beta_\varepsilon,\varepsilon),\quad
 r_{y\ell}=-\frac{\alpha_\varepsilon}{\varepsilon}
       f_R(-\varepsilon/\alpha_\varepsilon,0,\varepsilon).
 \tag{CJ2}
\]
The following exact row operations have regular limits:
\[
 \begin{aligned}
 \widehat r_{\rm old}
    &=r_{xy}+r_{x\ell}/\beta_\varepsilon
       \longrightarrow \partial_y f_R/\beta_0,\\
 \widehat r_{\rm value}
    &=-\varepsilon r_{x\ell}/\beta_\varepsilon
       \longrightarrow f_R,\\
 \widehat r_{\rm tangent}
    &=\alpha_\varepsilon r_{x\ell}-\beta_\varepsilon r_{y\ell}
       \longrightarrow \alpha_0\partial_y f_R-\beta_0\partial_x f_R .
 \end{aligned}
 \tag{CJ3}
\]
All derivatives and values on the right are at the collision. The
parameter derivative cancels in the difference quotients. The row
change has determinant \(\varepsilon\) per output coordinate, hence
\(\varepsilon^2\) for the two independent zero-sum outputs.

Partition the actual matrix as
\[
 M=\begin{pmatrix}A&V\\W&U\end{pmatrix},\qquad H=A-VU^{-1}W,
 \tag{CJ4}
\]
where the old and new observations are the row blocks, and retained
and new columns are the column blocks. The first operation in (CJ3)
adds new rows to an old row, and the other two change only the new
row basis. Consequently the Schur matrix is exactly unchanged:
\[
 H=\widehat A-\widehat V\widehat U^{-1}\widehat W,\qquad
 \det\widehat M=\varepsilon^2\det M,\quad
 \det\widehat U=\varepsilon^2\det U.
 \tag{CJ5}
\]
If \(\widehat U(0)\) is invertible, \(H\) has a finite limit equal to
this numerator-jet Schur complement. There is no nonzero negative-pole
coefficient to isolate under that hypothesis. Its constant coefficient
still contains the full correction term.

If three time vectors are collinear in the common-\(G\) model, the
same-state line determinant factors as the time-vector determinant
times the product of the three entries of that row of \(G\).
Generically there are then three simultaneous same-state collisions,
with separate crossing points. Their combined determinant multiplier
is \(\varepsilon^6\), not the single-collision \(\varepsilon^2\).

## A finite counterexample to pairwise triangular transport

Take \(G=I+\mathbf1\mathbf1^\top\), old time weights
\((1,2,3)\), \((1,5,7)\), and new earliest weights
\[
 (1,4/11+16\varepsilon/11,2).
 \tag{CJ6}
\]
The selected old lines are \(x=L_{1,0}\), \(y=L_{2,1}\). Their
crossing and the new row-zero line are
\[
 P=(1,11/16,-9/8),\qquad
 \ell=\varepsilon+(12/11-7\varepsilon/11)x
                       +(-2/11+3\varepsilon/11)y.
 \tag{CJ7}
\]
The exact checker constructs all actual columns
\[
 F_{t,s,a,b}=X_aK_t(a,b)
   \left(e_b-e_bK_s\prod_{j\notin\{t,s\}}^\nearrow K_j\right),
 \tag{CJ8}
\]
in order \(N,B,T\). The resulting jet matrix is \(54\) square:
36 new columns and 18 retained old columns. The old matrix is 18 square.
For the three colliding pair observations, the program uses (CJ3).
Every other pair is evaluated by exact denominator clearing.

The actual single-pole heads vanish after pair clearing. After triple
clearing they contain the two other selected lines, so their value
and both first derivatives vanish. The verifier checks these facts
for all 54 columns, instead of silently replacing full sources by
completed rows.

Let pair \(A=(L_{1,0},L_{2,0})\) and pair
\(B=(L_{1,0},L_{2,1})\). Their natural two-column groups in \(D_2\)
are \((F_{1,2,0,0},F_{2,1,0,0})\) and
\((F_{1,2,0,1},F_{2,1,1,0})\), respectively. The off-diagonal
blocks of \(D_2\) between these groups are exactly zero. However,
modulo the fixed prime \(1000003\),
\[
 \det\widehat U(0)=313525,\qquad \det D_2=998770,
 \tag{CJ9}
\]
and two scalar entries in the opposite off-diagonal blocks of \(H(0)\)
are
\[
 H(0)[0,1]=559830,\qquad H(0)[2,0]=284986.
 \tag{CJ10}
\]
The corresponding bordered determinants are \(174190\) and \(967603\).
Each is divided by \(313525\), using the exact bordered Schur identity.
All rational denominators are units modulo the fixed prime.

Both blocks are therefore nonzero over the rationals. Their directed
two-cycle prevents a simultaneous permutation of whole pair blocks
from making this matrix block triangular. Invertible changes within
each row and column pair cannot turn a nonzero block into zero.
This does not rule out general mixing between pairs or another
specialization.

## Reproduction and scope

Run from the project directory:

    python3 exploration/source24_collision_jet.py \
      --output certificates/source24_collision_jet.json

The portable standard-library verifier passed 187 exact checks.
It saves the complete rational matrices, source jets, 247 nonzero
division factors, 336 denominator units modulo the fixed prime, and
four modular elimination certificates with exact operation replay.
The recorded run took 0.33 seconds overall and 19.4 MB peak RSS.
The original exploratory calculation was independently reconstructed;
its downloaded program is not a runtime dependency.

The local observation identities and Schur invariance are paper
arguments; the finite arithmetic certificate is external, not a
Lean theorem. A full-source proof using this degeneration must still
control the entire transverse-jet correction.

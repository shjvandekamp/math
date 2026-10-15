# Raw completed rows and an ambient append criterion

**Status: audited paper reductions and external finite certificates.** No
uniform raw-row or source-family independence theorem is claimed. Use the
geometry and wide ambient space from `SOURCE24_TERMINAL_PEELING.md`.

The raw completed rows are

\[
 \widehat Q_{t,s,a,b}=X_aK_t(a,b)e_bP_s^{\widehat t}.
 \tag{A1}
\]

Their linear coefficients are parameter-only constants. Raw-row
independence is weaker than invertibility of the actual source residue
matrix. The conic example makes this distinction concrete: at three blocks,
the raw rows have generic rank 54 while their residue matrix has rank 51,
as proved in `SOURCE24_CONIC.md`.

## A global row-sum reduction

For source coefficients y, put J_(t,a,b)=sum_(s!=t) y_(t,s,a,b).
Since every transition has row sum one,

\[
 \sigma(\widehat Qy)=\sum_{t,a}\frac{X_a}{L_{ta}}
                 \sum_b A_t(a,b)J_{t,a,b}X_b. \tag{A2}
\]

Distinct line poles force a zero row sum exactly when

\[
 J_{t,a,0}=J_{t,a,1}=J_{t,a,2}=:k_{ta},\qquad
 \sum_t k_{ta}=0\quad(a=0,1,2). \tag{A3}
\]

For each line, its residue vanishes only if the displayed linear form is
proportional to L_ta. After cancelling those poles, the remaining polynomial
is sum_(t,a) k_ta X_a, giving the last three constraints. The incidence
map onto all 9m values J is surjective, so the raw row-sum map has rank
6m+3. Its coefficient kernel has dimension 9m(m−1)−6m−3 for m>=2.

Let I denote the prefix row X_a K_t(a,b)e_b. Under A3,

\[
 Iy=-\sum_{t,a}k_{ta}E_{ta},\qquad E_{ta}=X_ae_a(I-K_t). \tag{A4}
\]

Indeed I y=sum k_ta X_a e_a K_t, and its diagonal polynomial term
vanishes by the last condition in A3. Thus a raw relation would yield
F y=−sum k_ta E_ta. This exact restriction does not eliminate the
remaining functional relation.

## A stronger append criterion without an old-source inverse

Set m=q+1. Interior raw rows satisfy Qhat_m=Qhat_q K_m exactly. It
would therefore suffice to prove that the 18q boundary raw rows, with
t=m or s=m, are independent modulo the entire appended ambient space

\[
 S_m(\widehat W_q)=\{R K_m:R\in\widehat W_q\}. \tag{A5}
\]

This is stronger than independence modulo the old raw-row span. Right
multiplication by K_m is injective over the rational-function field.
An explicit frame of wide W_q consists of both directed rows

\[
 E_{i\to j}=\frac{A_u(c,d)X_cX_d}{L_i}
                  \left(e_d-\frac{v_j}{L_j}\right)
 \quad(i=(u,c),\ j=(v,d),\ u\ne v), \tag{A6}
\]

at each unordered cross-pair, all 9q rows V_i,b from the completion note,
and the three diagonal rows X_d e_d. Its size is 9q²+3. The two pair
orientations isolate independent pair-residue vectors; V supplies the
axis values, and the diagonals supply vertex values. This is an actual
ambient frame, not a replacement for the raw boundary sources.

The stronger condition fails at q=1: every first-new raw row is
(V_(t,a,b)+delta_ab X_a e_a)K_m and already belongs to A5. A later base
is therefore needed. At q>=2 the sufficient condition remains open in
general.

## The observation count must respect row-sum relations

Row sums of the appended frame and raw boundary columns lie in

\[
 \mathcal S_m=\operatorname{span}\{X_aX_b/L_{ta},X_0,X_1,X_2\},
 \qquad \dim\mathcal S_m=6m+3. \tag{A7}
\]

Each line contributes two independent quadratic residues divisible by
X_a: the third combination is the polynomial X_a after weighting by
A_t(a,b). Distinct lines separate these residue spaces, and the three
linear polynomials complete the count. Appending a stochastic kernel
preserves row sums. These raw boundary rows belong to wide W_m: each
block occurs once, coordinate and matching factors persist, same-block
double residues vanish, cross-pair sums vanish, and vertices have the
allowed diagonal values.

At N ordinary effect points, replace the third component observation by
the row sum. The resulting evaluation rank obeys

\[
 \operatorname{rank}(\mathrm{evaluation})\le
             2N+\min(N,6m+3). \tag{A8}
\]

Thus three component evaluations per point cannot be counted as three
independent rows once N>6m+3. At m=5 and N=85 the upper bound is 203,
so this sampling scheme cannot certify a 219-column target. This explains
the original rank-203 test without asserting a functional dependence.

## Exact finite certificates

`exploration/source24_raw_boundary.py` constructs A6, V, and the diagonal
rows, appends K_m, and evaluates the original 18q raw boundary words at
recorded ordinary points. The saved JSON contains the points, hashes,
parameter fixtures and exact modular minor certificates. The primary
researcher reviewed the frame, source order, and evaluator. The improved
default uses at least ceil(target/2)+12 points; historical undersampled
cases are explicitly identified.

| q | Fixture | Appended old-frame rank | Combined rank / target |
|---:|---|---:|---:|
| 1 | economic | 12 | 21 / 30 |
| 2 | economic | 39 | 75 / 75 |
| 3 | economic | 84 | 138 / 138 |
| 3 | independent time factors | 84 | 138 / 138 |
| 4 | economic, 170 points | 147 | 219 / 219 |

The q=1 containment identity is independently checked at the evaluation
points. Full nonzero minors at q=2,3,4 lift from the recorded prime to
characteristic zero after denominator clearing. They prove the stronger
condition separately at those fixed parameter fixtures. The 85-point
q=4 economic and independent tests both attain their sampling cap 203;
their deficiency is not evidence of a raw-row relation.

The primary researcher derived A2–A4 and A8. An independent Astra
researcher checked them, the ambient-frame construction and the append
criterion. The same researcher proposed the stronger criterion A5.
Uniform nonvanishing of its boundary matrix, and the additional
transversality needed for the actual source family, remain unresolved.

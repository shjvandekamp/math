# Verified statements and scope

**Both main declarations pass compilation, clean source rebuilds, axiom
checks and independent compiled-statement audits.** The evidence and
reproduction commands are recorded in VERIFICATION.md.

## Model and finite basis theorem

Use paper labels q,r in {1,2,3}, t in {1,2,3,4}, and fix initial state y0.
Let pi_t(q,r)>0 and eta=(1,eta2,eta3), eta2,eta3>0. Define

\[
 L_{tr}(\eta)=\sum_q\pi_t(q,r)\eta_q,\qquad
 p_y(\eta)=\prod_{t=1}^4\frac{\pi_t(y_t,y_{t-1})\eta_{y_t}}{L_{t,y_{t-1}}(\eta)}.
\]

The moment space is M={m in R^81 : sum_y m_y p_y(eta)=0 for every positive
(eta2,eta3)}. The initial condition is conditioned on, never integrated out.

Set A_y=product_t pi_t(y_t,y_(t−1)) and

\[
 F_y^0=\left(\prod_t\eta_{y_t}\right)
       \prod_{t=2}^4\prod_{r\ne y_{t-1}}L_{tr},\quad
 D=L_{1,y_0}\prod_{t=2}^4\prod_rL_{tr}.
\]

Then p_y=A_y F_y^0/D. Let C0 be the 66-by-81 coefficients of F_y^0 after
eta1=1, ordered as in `exploration/exact_q3t4.py`. The actual restriction
matrix is C=C0 diag(A_y).

Let Msrc be the 33-by-81 source moment matrix, with generation orders and
indicator values explicitly listed in `q3t4-certificate.json`, and
K=Msrc diag(A_y). Its entries are polynomial differences of transformed path
numerators. For the formal certificate, let E be the 48-by-48 matrix obtained
by evaluating F_y^0 at the fixed positive integer effect pairs and path columns
in `formal/PanelMoments/WitnessData.lean` (`evaluationPoints` and
`evaluationPaths`). Let K_r' select the 33 rows `sourceRows` and the fixed
33 path columns `sourcePaths r` from the source-numerator matrix for initial
state r. All row and column lists are fixed independently of the parameter.
The generator `exploration/generate_lean_witness.py` reproduces these lists
and inverse certificates modulo 11. The earlier coefficient minor in
`q3t4-certificate.json` remains a separate exact discovery certificate.

Define the explicit polynomial

\[
 \Delta(\pi)=\det E(\pi)\prod_{r=1}^3\det K_r'(\pi).
\]

**Finite theorem.** If pi is positive and Delta(pi) is nonzero, for every
initial state the 33 indexed source moments are a basis of M, and dim M=33.
The proof derives validity universally, rank C>=48 through evaluation of
the cleared polynomials, and rank K=33 from the fixed source minors. Equality
of the kernel and the span then follows by dimension. Universal validity
and the concrete certificates and finite integration are now Lean checked.

## Economic domain and genericity

Use one scalar covariate, with

\[
 \pi_t(q,r)=\exp(\gamma_{qr}+x_t\beta_q),\quad
 \gamma_{1r}=\gamma_{q1}=0,\quad\beta_1=0.
\]

The parameter space is R^10: four unnormalized gamma entries, two slopes,
and four covariates. An exact model-consistent witness is

\[
 \gamma_{qr}=(q-1)(r-1)\log 2,\quad \beta_q=q-1,\quad x_t=3t\log2.
\]

Thus pi_t(q,r)=2^((q−1)(3t+r−1)). All four determinants in Delta are nonzero
at this witness in the external exact calculation; Lean has checked their
reductions and explicit right inverses modulo 11 from the model formulas.
Delta after substitution is real analytic, hence its nonzero set is open
and dense: on the line from an arbitrary parameter to the witness, the
analytic function is nonzero at the endpoint and cannot vanish on a
neighborhood of the starting point. The general analytic identity-theorem
infrastructure and the concrete minor application now compile.
No claim of genericity for every fixed x or every fixed
beta is intended; the declared domain varies jointly over R^10.

## Structural extension

For Q=3 and arbitrary T>=1, put d=3T−2. Six projective base points per time
t>=2 give independent evaluation conditions on homogeneous degree-d
polynomials under explicit separation conditions. Consequently

\[
 \operatorname{rank}C=\binom{3T}{2}-6(T-1),\qquad
 \dim M=3^T-\binom{3T}{2}+6(T-1).
\]

This addresses the coefficient-relations gap identified in source Appendix A.
The equality argument via products of cubic spaces is fully Lean checked,
including its graded algebra, interpolation induction, actual likelihood
bridge, and explicit nonempty open dense economic region. The joint economic
domain is R^(T+6): four state-dependence coefficients, two slopes, and T scalar
covariates, with the same normalizations and power-of-two witness as above.
The explicit product defining the structural region is displayed in
MANUSCRIPT.md; it contains only primitive geometric nonvanishing factors.

The two main declarations are:

- `PanelMoments.three_choice_four_period_generic_completeness` in
  `formal/PanelMoments/EconomicGenericity.lean`: independence, spanning and
  dimension 33 for the specified source family on its finite generic region.
- `PanelMoments.StructuralCompleteness.three_choice_generic_moment_dimension`
  in `formal/PanelMoments/StructuralCompleteness.lean`: the displayed dimension
  for every T>=1 and every initial state on its structural generic region.

The finite and structural regions are independently defined sufficient regions;
no equality or inclusion between them is asserted. In Lean, dimension uses
natural numbers, so subtraction is grouped as
`(3^T + 6*(T-1)) - (3*T).choose 2`. The proved additive identity
`dim M + (3*T).choose 2 = 3^T + 6*(T-1)` establishes the usual integer formula
without relying on truncated subtraction in the wrong order.

Independence of the particular DHW source family for arbitrary T is not proved
by this dimension theorem. Nor is genericity on every fixed-covariate or
fixed-slope slice, a measure-zero exceptional-set claim, or an arbitrary-Q
extension asserted.

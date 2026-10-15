# A fixed-mesh tail obstruction for an explicit fractional-Adams reference scheme

Research manuscript, 2026-10-15. Proof status is governed by VERIFICATION.md and STATUS.md. The complete pricing objective remains open.

## Scope

We investigate the standard single-prediction/single-correction fractional-Adams recurrence reconstructed from El Euch–Rosenbaum §5.1, paired with the composite-trapezoidal exponent explicitly specified by Ben Hammouda et al., arXiv:2609.00438v1, Eq. (13). THEOREM.md gives every coefficient and convention. The main authors' executable was not located; this is an explicit reference-scheme extension, not a claim to have verified their unpublished code. Earlier literature already documents Adams instability. The checked contribution is its exact all-finite-mesh mechanism and resulting deterministic domination obstruction. Novelty remains provisional.

## Algebraic theorem and proof

Fix alpha in (1/2,1), delta>0, V0>0, c=(gamma nu)^2/2>0. Let a=delta^alpha/Gamma(alpha+2)>0 and b=delta^alpha/Gamma(alpha+1)>0. All other model coefficients and R are real. Let xi=u+iR. Write F(xi,z)=q(xi)+l(xi)z+c z², where q has degree 2 and leading coefficient -1/2, while l has degree at most 1.

For each n>=1, the corrected node h_n is a polynomial in u of degree d_n=4^n, with positive real leading coefficient L_n. Specifically L1=a c b²/4 and L_(n+1)=a b² c³ L_n^4.

At n=0 the only history value is h0=0. The predictor is bq, of degree 2 and leading coefficient -b/2. F(xi,bq) has degree 4 and leading coefficient c b²/4; the corrector history term has degree 2, so cannot cancel it. This proves the first step. For n>=1, F(xi,h_n) has degree 2d_n and leading coefficient c L_n², since 2d_n exceeds both d_n+1 and 2. Earlier F values have strictly smaller degrees. The newest predictor coefficient is b, so the predictor has leading coefficient b c L_n² and degree 2d_n. Its F evaluation has degree 4d_n and leading coefficient b²c³L_n^4. The corrector history has degree at most 2d_n and cannot cancel it. Multiplication by a proves the induction.

Set J(xi,z)=theta gamma z+V0F(xi,z). The final endpoint uniquely has maximal degree 2d_M in the trapezoid. Therefore the real polynomial P_M(u)=Re G_M(u+iR) has degree d=2·4^M and leading coefficient C=delta V0 c L_M²/2>0. Translation by iR and the drift term do not change that highest coefficient. This proof covers every finite M>=1, not merely one coarse mesh.

## Nonintegrability consequence

Let f:[0,infinity)->C be any bounded comparison transform, with |f(u)|<=B. This deterministic hypothesis is separate from identifying f with a stochastic rough-Heston transform. For K>0, R<-1, the specified call-transform formula has modulus

K^(1+R)/sqrt((u²+R²)(u²+(R+1)²)).

Write P_M=C u^d+sum_(k<d)p_k u^k and S=sum_(k<d)|p_k|. For u>=max(1,2S/C), P_M>=C u^d/2. Also the denominator above is at most A u² for u>=1, with A=sqrt((1+R²)(1+(R+1)²)). Since exp(x)>=x,

|exp(G_M)-f|>=C u^d/2-B.

For sufficiently large u this is at least A K^(-1-R)u². The weighted modulus error is therefore at least 1 on a half-line and is not Lebesgue integrable. This reasoning uses an analytic lower bound, never floating-point overflow.

For any hierarchy M_l=2^l M0 and any finite positive normalization exponent p, a nonnegative measurable function dominating all delta_l^(-p)|P-hat||f-Phi_l| cannot be integrable: select any one included level. No fixed refinement threshold removes the obstruction. An extended-real supremum avoids any issue of representing an unbounded supremum as a real number.

This is not a theorem about the integral of the real part, which may oscillate. It is the modulus domination specifically required by Eq. (20).

## Nondegenerate moment example: external financial bridge

Choose alpha=3/4 (H=1/4), gamma=nu=theta=V0=S0=K=T=1, rho=-1/2, r=0, R=-2. The scalar moment Riccati polynomial is 1-2h+h²/2; its smaller positive root is 2-sqrt(2). Case (C), Proposition 3.6 and Theorem 2.4 of [Gerhold–Gerstenecker–Pinter, arXiv:1801.09458](https://arxiv.org/html/1801.09458), imply boundedness and absence of moment explosion. On 0<=h<=2-sqrt(2), J(h)=1-h+h²/2<=1, yielding E[S_T²]<=exp(T) from the affine moment identity. Thus the line R=-2 is admissible on paper, and for T=1 the exact transform is bounded by e.

The genuine payoff integral at K=1/R=-2 is Lean-checked. These stochastic existence, moment, and affine-identity steps are NOT yet part of the Lean dependency chain. The example must not be described as an end-to-end formally verified financial counterexample.

## A limited cutoff repair, with initial-time singularity respected

The following analytic route is supporting work, not presently a Lean theorem. On 0<=u<=U define A=sup|q(u+iR)|, B=sup|l(u+iR)|, choose Q>0, put M=A+BQ+cQ², L=B+2cQ, and kappa=T^alpha/Gamma(alpha+1). If kappa M<=Q and kappa L<1, the Volterra map contracts the radius-Q ball. Positive Adams weights with row sums t^alpha/Gamma(alpha+1) preserve the same ball for prediction and correction.

The exact solution is alpha-Hölder with constant Hc=2M/Gamma(alpha+1), directly from splitting the fractional integral. Predictor and interpolatory-corrector exact-data defects are at most L Hc kappa delta^alpha. With a=delta^alpha/Gamma(alpha+2), maximum nodal error satisfies

E<=C_h delta^alpha, C_h=L Hc kappa(1+kappa L)/(1-kappa L).

This follows because the history plus predicted-endpoint propagation coefficient is L(kappa_t-a)+a L²kappa_t<=kappa L. The trapezoidal integration has order at least alpha from Hölder continuity; with L_J=theta gamma+V0L, its exponent error is at most T L_J(C_h+Hc)delta^alpha. For positive theta,gamma, the uniform exponent bound produces a computable truncated-transform error constant. Neither order uses a plotted slope or differentiability at zero.

For the moment example and K=1, the exact Fourier tail beyond U is at most e/(pi U), using the quadratic call-transform decay. However, the ball conditions become restrictive as U grows. This local-time, finite-band estimate does not supply arbitrary pricing accuracy at a fixed maturity. Validated continuation, global finite-band stability, quadrature, and roundoff remain open.

## What is not resolved

The conditional conjecture's antecedents, the precise author-code variant, global pointwise nodal rates for the full model, a useful arbitrary-tolerance repair, and the machine-checked stochastic-to-price bridge have not been established. No statement about SPX-to-VIX extension is made.

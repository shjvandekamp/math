# A fixed-mesh tail obstruction and validated finite-band convergence

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

## Checked consistency, including the initial singularity

On 0<=u<=U, explicit coefficient bounds A and B give M=A+BQ+cQ² and L=B+2cQ on the radius-Q ball. Every predictor and corrector weight is nonnegative. Both full rows sum exactly to t_n^alpha/Gamma(alpha+1); the corrector history row omits precisely the endpoint a=delta^alpha/Gamma(alpha+2).

For an actual continuous solution h=I^alpha F with |F(h)|<=M, splitting the actual singular-kernel integral gives alpha-Hölder constant Hc=2M/Gamma(alpha+1). This includes t=0. The predictor is exact product integration of a piecewise constant interpolant. The corrector is exact product integration of the affine interpolant, including the endpoint. Thus both exact-data defects are at most epsilon=D*delta^alpha, D=L*Hc*T^alpha/Gamma(alpha+1). The kernel integrability, cell coefficient identities, interpolation estimates and row assembly are all checked. No classical derivative at zero or residual bound is assumed.

The original local argument is also checked: if kappa*M<=Q and kappa*L<1, with kappa=T^alpha/Gamma(alpha+1), both numerical stages stay in the ball and E<=epsilon*(1+kappa*L)/(1-kappa*L). Separately, these conditions make the actual Volterra map a contraction on a closed ball of continuous paths, proving local existence and uniqueness. This local argument alone cannot handle large fixed maturity.

## Checked validated continuation at fixed maturity

Assume an actual exact solution family on [0,U]×[0,T] with |h|<=Q0, and enlarge the ball to Q=Q0+eta for eta>0. The exact-path existence and bound remain explicit hypotheses of the arbitrary-maturity result. Use W_n=exp(lambda*t_n). Actual kernel integration proves

```text
sum_(j<n) b_jn*W_j <= W_n*lambda^(-alpha),
sum_(j<n) a_jn*W_j <= W_n*exp(lambda*delta)*lambda^(-alpha).
```

Choose lambda=(8*max(1,L))^(1/alpha), so L*lambda^(-alpha)<=1/8. Impose exp(lambda*delta)<=2 and a*L<=1. The predictor propagation coefficient is at most W_n/8. The combined corrector-history and predicted-endpoint coefficient is at most 3W_n/8. If all previous node errors are <=4*epsilon*W_j, then the predictor error is <=3*epsilon*W_n/2. The margin condition 4*epsilon*exp(lambda*T)<=eta puts this predictor inside the enlarged ball before the Lipschitz estimate is invoked. The corrected error is then <=4*epsilon*W_n. Strong induction keeps the entire old history and proves the bound at every node.

Consequently Ch=4*D*exp(lambda*T) gives E<=Ch*delta^alpha on a fixed maturity interval. THEOREM.md records an explicit positive mesh threshold satisfying all conditions. An Archimedean argument supplies one positive integer base mesh working for every dyadic refinement and every frequency in the band. This removes the condition kappa*L<1 from the numerical continuation theorem; it does not construct a global exact solution.

The actual polynomial exponent evaluates to the specified trapezoidal sum. With LJ=|theta*gamma|+|V0|L, its nodal perturbation plus derived Hölder quadrature error is at most Cg*delta^alpha, where Cg=T*LJ*(Ch+Hc). Exponentiation yields the explicit Cphi in THEOREM.md, uniformly in the band and level. A common affine phase leaves exponent error unchanged and scales exponential error by exp(-R*m). These are proved conservative rates q=rT=alpha, rather than claims of optimal order.

The theorem is nonvacuous: for alpha=3/4, R=-2, gamma=nu=theta=V0=1, rho=-1/2, U=Q0=1 and tau=(Gamma(7/4)/16)^(4/3), the exact Volterra solution family is constructed. The kernel mass is 1/16, M=9 and L=7/2. The constructed family and a validated dyadic seed satisfy nodal, exponent and exponential error bounds of order delta^(3/4). The seed is existential from explicit real expressions; a numerical integer enclosure has not been generated.

## Checked global construction and exact exponent bound

The fractional semigroup I^beta I^alpha=I^(alpha+beta) is checked for positive orders and continuous complex paths, including the singular kernels' Beta/Gamma normalization and absolute integrability needed by Fubini. Applied to the actual equation, it gives integral F(h)=I^(1-alpha)h(T). Therefore

```text
G = theta*gamma*integral_0^T h(t)dt + V0*I^(1-alpha)h(T).
```

If Re h<=B, theta*gamma>=0 and V0>=0, positivity of the kernels yields the checked bound

```text
|exp(G)| <= exp(B*(theta*gamma*T + V0*T^(1-alpha)/Gamma(2-alpha))).
```

For the concrete parameters the checked algebra gives Re F(u,1+iy)=-1/2-3u²/8-(y-u/2)²/2<0 and, when Re z<=1, Re(conj(z)F(u,z))<=|q(u)|*|z|-3|z|²/2. The required maximum principle and global construction are now checked.

The regularity step is stronger than ordinary alpha-Hölder continuity. At each positive time t, I^alpha f has arbitrarily small left alpha-Hölder constant when f is continuous. Freeze f(t) on a short recent interval. The old history and frozen constant are Lipschitz near t; the remaining recent force is uniformly small and has a correspondingly small fractional Hölder constant. A positive-power threshold absorbs the Lipschitz term. This derives the local little-Hölder property without an ordinary derivative of h.

For a real part attaining a positive past maximum, split I^(1-alpha)v(t)-I^(1-alpha)v(t-epsilon) into the complete old history and recent interval. Kernel monotonicity and the maximum property give a lower bound by the constant-path increment minus the recent deficit. The local little-Hölder estimate controls that deficit. The complementary identity and continuity of f then force Re f(t)>0. First contact with Re h=1 contradicts the strict inward force. First norm contact is handled by the fixed linear functional Re(conj(h(t_*))*h(s)), avoiding a fractional chain rule for the norm. This gives |h|<A_U+1 for A_U=bandConstantBound(-2,U).

To establish existence, clamp each component of z to [-Q,Q], Q=A_U+1. This continuous map is the identity on |z|<=Q, has norm at most 2Q, and Lipschitz constant at most 2. The resulting force is globally Lipschitz. On continuous paths, conjugate the full Volterra operator by exp(lambda*t). The weighted kernel mass is at most lambda^(-alpha), so an explicit lambda makes the operator a contraction on the entire path space at any finite T. At a hypothetical first norm contact with Q, its complete preceding history satisfies the original equation, contradicting the strict norm bound. Thus the cutoff never activates. This constructs the actual solution for every real frequency and every finite T, with Re h<1.

With theta=gamma=V0=1, the exact deterministic exponential therefore satisfies |Phi|<=B(alpha,T)=exp(T+T^(1-alpha)/Gamma(2-alpha)), uniformly over frequency. Its frequency continuity follows from the proved uniform convergence on every finite band. The call-weighted exact Fourier integrand is absolutely integrable.

The all-original-level nodal rate is obtained by applying the validated estimate to a sufficiently fine tail of each prescribed hierarchy and absorbing its finitely many coarse errors. The exact-node trapezoidal quadrature rate, which is source Assumption 5, is separately derived from J's Hölder regularity with constant T*LJ*Hc. It is distinct from the total numerical exponent error. Strictly positive source constants are obtained by enlarging the finite nonnegative estimates. Thus q=rT=alpha is proved for the actual deterministic family, while the original domination still has infinite integral at pG=alpha.

For each cutoff U>0, the actual deterministic Fourier integral and its truncated Adams approximation satisfy error<=U*Cphi*delta^alpha/2+B(alpha,T)/U on a validated dyadic family. Both integrands' measurability and integrability are established. This is a cutoff-and-time-discretization repair; evaluation of the truncated integral, quadrature and rounding are separate.

For the external moment example and K=1, the on-paper exact Fourier tail beyond U is at most e/(pi U). This financial statement still depends on the external stochastic moment/affine identity. General call-factor bounds and deterministic cutoff estimates do not supply that missing identification.

## What is not resolved

The precise author-code variant, stochastic antecedents, an arbitrary-tolerance price algorithm with evaluated certificates, and the machine-checked stochastic-to-price bridge have not been established. Global deterministic existence/barriers, the source rates and the deterministic cutoff repair are now proved for the concrete coefficients. General coefficients retain explicit exact-solution hypotheses. No statement about SPX-to-VIX extension is made.

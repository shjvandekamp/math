# Theorem contract — 2026-10-15

## Source convention and intended model

Source: Ben Hammouda, Ben Romdhane, Samet, Tempone, arXiv:2609.00438v1, §§2–3 and Appendix H. Let alpha=H+1/2 in (1/2,1), gamma,nu,theta,V0,T,S0,K>0, rho in [-1,1], r real, X0=log S0. Brownian motions have correlation rho; the variance kernel is t^(alpha-1)/Gamma(alpha), drift gamma(theta-V), diffusion gamma nu sqrt(V). The log-price extended transform is Phi(xi)=E exp(i xi X_T). Payoff transform uses exp(-i xi x), and for a call P(x)=(exp(x)-K)+ is -K^(1-i xi)/(xi^2+i xi). The contour is xi=u+iR, R<-1; E exp(-R X_T)<infinity is a separate, still unproved admissibility obligation.

F(xi,z)=-(xi^2+i xi)/2+gamma(i xi rho nu-1)z+(gamma nu)^2 z^2/2. The exact Riccati equation is h=I^alpha F(xi,h), h(0)=0, and the exact exponent is i xi(X0+rT)+integral_0^T [theta gamma h+V0 F(xi,h)]dt.

## Explicit algorithm under audit

For integer M>=1, delta=T/M, h_0=0. For n=0,...,M-1,

- b_(j,n+1)=delta^alpha/Gamma(alpha+1) * ((n+1-j)^alpha-(n-j)^alpha), 0<=j<=n.
- a_(0,n+1)=delta^alpha/Gamma(alpha+2) * (n^(alpha+1)-(n-alpha)(n+1)^alpha).
- a_(j,n+1)=delta^alpha/Gamma(alpha+2) * ((n-j+2)^(alpha+1)+(n-j)^(alpha+1)-2(n-j+1)^(alpha+1)), 1<=j<=n.
- a_(n+1,n+1)=delta^alpha/Gamma(alpha+2).
- predictor p_(n+1)=sum_(j=0)^n b_(j,n+1)F(xi,h_j).
- corrected h_(n+1)=sum_(j=0)^n a_(j,n+1)F(xi,h_j)+a_(n+1,n+1)F(xi,p_(n+1)).

These specify a single explicit predictor evaluation and a single corrector evaluation, in exact complex arithmetic. No implicit root solve, clipping, or frequency cutoff is present. Identification with the authors' numerical code remains under audit; the main paper references the method rather than printing its recurrence.

Set J(xi,z)=theta gamma z+V0F(xi,z). G_M=i xi(X0+rT)+delta[J(xi,h0)/2+sum_(j=1)^(M-1)J(xi,hj)+J(xi,hM)/2], Phi_M=exp(G_M). This integration is explicitly specified in source Eqs (11)–(13).

For M0>=1, M_l=2^l M0 and delta_l=T/M_l. The requested domination is D_R(u)=sup_l delta_l^(-pG)|P-hat(u+iR)||Phi(u+iR)-Phi_(M_l)(u+iR)|, pG=min(q,rT). The positive result below derives the conservative rates q=rT=alpha on a validated dyadic family from the actual integral equation; neither rate is assigned an empirical value.

## Deterministic theorem and exact checked scope

For every alpha in (1/2,1), real R,rho,theta,X0,r, positive gamma,nu,V0,T, and integer M>=1, the above polynomial recurrence has deg_u h_M=4^M with positive real leading coefficient L_M. Write c=(gamma nu)^2/2, b=delta^alpha/Gamma(alpha+1), a=delta^alpha/Gamma(alpha+2). Then L_1=a c b^2/4 and L_(n+1)=a c^3 b^2 L_n^4. The real part of G_M has degree 2*4^M and leading coefficient delta V0 c L_M^2/2>0. Consequently no fixed M can make the discrete transform globally bounded on a horizontal contour.

The checked analytic consequence specializes to K=1, R=-2, S0=1, r=0: against any globally bounded comparison function Phi:R→C, the modulus error multiplied by the genuine call transform is not integrable on (0,infinity). The true payoff integral identity is also checked. The concrete all-level supremum has infinite extended Lebesgue integral for every real normalization exponent p, and no integrable majorant exists even after removing any fixed number of levels. No empirical convergence order is used. This does not establish the moment domain, stochastic model identity, or every premise of the conditional conjecture.

A concrete nondegenerate algebraic example is H=1/4, gamma=nu=theta=V0=T=S0=K=1, rho=-1/2, r=0, R=-2. These satisfy the listed numerical parameter inequalities. The literature establishes moment admissibility for this example (see MANUSCRIPT.md); the stochastic moment bridge is NOT presently Lean-checked.

## Checked finite-band repair at fixed maturity

Let 0<alpha<1, T>0, U>=0, Q0>=0, eta>0, and let all model coefficients be real. Suppose h(u,t) is an actual continuous solution of h=I^alpha F for every u in [0,U], with |h(u,t)|<=Q0 for t in [0,T]. `IsRiccatiSolution` contains exactly continuity and this integral equation. It contains no error estimate, stability condition or existence assertion.

Set Q=Q0+eta, c=(gamma nu)^2/2 and

```text
A = ((U+|R|)^2 + U+|R|)/2
B = |gamma|*((U+|R|)*|rho|*|nu| + 1)
M = A+B*Q+c*Q^2
L = B+2*c*Q
kappa = T^alpha/Gamma(alpha+1)
Hc = 2*M/Gamma(alpha+1)
D = L*Hc*kappa
lambda = (8*max(1,L))^(1/alpha)
Ch = 4*D*exp(lambda*T)
LJ = |theta*gamma|+|V0|*L
Cg = T*LJ*(Ch+Hc)
Cphi = exp(T*(|theta*gamma|*Q+|V0|*M)+Cg*T^alpha)*Cg
```

There exists a positive integer M0, chosen before any frequency, level or node, such that for every ell>=0, N=2^ell*M0, delta=T/N, u in [0,U], and 0<=n<=N:

```text
|h_n(u)-h(u,n*delta)| <= Ch*delta^alpha
|h_n(u)| <= Q
|G_N(u)-G(u)| <= Cg*delta^alpha
|exp(G_N(u))-exp(G(u))| <= Cphi*delta^alpha
```

Here G is the actual integral of J, and G_N is the actual polynomial/trapezoidal exponent already used in the negative theorem. These displayed exponential constants omit the affine drift; a common phase i(u+iR)m leaves exponent error unchanged and multiplies exponential error by exp(-R*m). Both identities are checked in `TransformError.lean`.

An explicit sufficient threshold for delta is the minimum of

```text
log(2)/lambda,
(Gamma(alpha+2)/max(1,L))^(1/alpha),
(eta/(4*max(1,D)*exp(lambda*T)))^(1/alpha).
```

`MeshConditions.lean` proves positivity of this threshold and existence of an integer dyadic seed satisfying it at every refinement. No numerical evaluation or floating-point enclosure of that seed is claimed. The proof uses the full old history. It proves the predictor remains in the enlarged ball before applying its local Lipschitz bound. There is no condition kappa*L<1 in the fixed-maturity numerical theorem.

`Approximation.lean` packages these estimates as `riccati_dyadic_band_error` and `riccati_dyadic_band_transform_error`. The true kernel product-integration errors and trapezoidal error are derived, not supplied as hypotheses. The initial singularity is handled by alpha-Hölder estimates on [0,T], including zero. `unweighted_error_implies_source_weighted` converts the nodal bound to the source's t^(alpha-1)*delta^alpha convention with factor T^(1-alpha).

`CoarseLevels.lean` additionally proves the source's frequency-wise rates for **any prescribed original M0>0 and every original level**, at each fixed u for which an actual bounded solution exists. It selects a sufficiently fine tail of that original hierarchy and absorbs the actual finitely many coarse errors into finite constants. The nodal time-weighted, exponent and exponential estimates have order alpha. No divisibility assumption relates the original base to the validated seed. These frequency-dependent constants need not be integrable over frequency; this result is consistent with the negative global domination theorem.

Local existence and uniqueness are proved separately by a continuous-path contraction: kappa*M<=Q and kappa*L<1 suffice. A fully constructed example has alpha=3/4, R=-2, gamma=nu=theta=V0=1, rho=-1/2, U=1, Q0=1 and positive maturity tau=(Gamma(7/4)/16)^(4/3). Its kernel mass is 1/16, force bound is 9 and Lipschitz constant is 7/2. `localExample_validated_transform` constructs the exact family and a positive base mesh, with all refinement errors of order delta^(3/4). This is deterministic nonvacuity, not a moment or price certificate.

For general coefficients the repair assumes existence of the bounded exact solution family. For the concrete coefficients below, the new global construction discharges these hypotheses. The fractional semigroup and complementary identity I^(1-alpha)I^alpha f=integral f are checked with their Fubini hypotheses in `FractionalSemigroup.lean`.

`TransformBound.lean` then proves the actual exponent identity G=theta*gamma*integral h+V0*I^(1-alpha)h(T). If Re h<=B, theta*gamma>=0 and V0>=0, it yields |exp G|<=exp(B*(theta*gamma*T+V0*T^(1-alpha)/Gamma(2-alpha))). The concrete construction proves B=1 sufficient at every frequency.

For the genuine K=1, R=-2 call factor, `FourierBounds.lean` proves |P-hat(u)|<=1/2 everywhere and <=1/u^2 for u>0. Its generic cutoff theorem gives an actual Fourier integral error <=U*E/2+B/U for U>0, given a band transform error E, integrable band products, and a measurable exact tail bounded by B. This is a deterministic integral theorem; no stochastic identity, Fourier inversion normalization or discounting is inserted.

## Global concrete deterministic construction

Fix 0<alpha<1 and any finite T>=0, with R=-2, gamma=nu=theta=V0=1 and rho=-1/2. `exists_concrete_global_riccati_family` constructs one family h(u,t), for all real u, satisfying the actual equation on [0,T]. For every u and t in that interval,

```text
Re h(u,t) < 1,
|h(u,t)| < bandConstantBound(-2,U)+1 whenever |u|<=U.
```

These are conclusions, not hypotheses. Local little-Hölder regularity is derived from the actual fractional integral; a backward-difference maximum principle and first-contact argument prove the half-plane and norm barriers. A square cutoff of the force is globally Lipschitz. Exponential conjugation of the complete-history Volterra operator constructs its fixed point on any finite interval. The norm barrier proves the cutoff never activates. No time restart drops memory, and no derivative of h at zero is assumed. The family is chosen for each finite T; consistency of choices across different maturities is not asserted.

For the actual deterministic exponential Phi(u)=exp(G(u)) this yields

```text
|Phi(u)| <= B(alpha,T) = exp(T + T^(1-alpha)/Gamma(2-alpha))
```

uniformly over all real frequencies. `BandContinuity.lean` derives frequency continuity from uniform convergence of the actual polynomial approximants. Consequently the genuine call-weighted exact Fourier integrand is absolutely integrable on (0,infinity).

In the intended rough range 1/2<alpha<1 and T>0, `exists_concrete_deterministic_obstruction` combines this construction with the original-level source rates q=rT=alpha and the infinite integral of D_R at pG=alpha, for every original M0>0. `ConcreteSourceRates` is an explicit conclusion about the actual recurrence, not a hypothesis or an abstract solver field. This closes the deterministic existence/rate/bounded-comparison gaps. The stochastic affine identity and moment domain remain outside this theorem.

For every U>0, the same exact family has a validated seed and all-refinement deterministic cutoff estimate

```text
|integral_(0,infinity) P-hat*Phi - integral_0^U P-hat*Phi_N|
  <= (U/2)*Cphi(alpha,T,U)*delta^alpha + B(alpha,T)/U,
```

where Cphi is the explicit earlier constant at Q=bandConstantBound(-2,U)+2. Integrability and measurability are derived for these actual objects. This supplies a cutoff-and-time-discretization repair for a deterministic Fourier integral, not a quadrature algorithm or an expected discounted payoff.

## Remaining financial objective

For this unchanged PECE recurrence, removing a fixed number of coarse levels cannot repair an obstruction that holds for every finite M. The checked repair couples the initial mesh to a finite frequency band. A pricing theorem still needs stochastic model-to-transform identity, moment admissibility, Fourier inversion, quadrature, rounding, and the final combined price-error inequality. Global exact-solution control for the concrete coefficients, the genuine payoff transform and the derived rates are already checked. No VIX extension is claimed.

## Formal declarations and limits

- `roughState_succ`: the polynomial evaluation obeys the explicit complex PECE recurrence with concrete weights.
- `adams_degree_and_leading`: exact node degree and positive real highest coefficient.
- `roughExponentWithDrift_degree_and_leading`: the general horizontal-contour exponent, including arbitrary affine phase, has degree 2·4^M and positive leading real coefficient.
- `vanillaCall_fourier_transform`: the defining Fourier integral of max(exp(x)-1,0) equals the rational call factor at R=-2.
- `reference_genuine_call_not_integrable`: fixed-mesh nonintegrability, with that defining payoff integral in the statement.
- `domination_lintegral_eq_top`: infinite integral of the actual extended-real all-level supremum for the explicit reference scheme.
- `no_integrable_majorant_after_fixed_level`: removing finitely many initial levels cannot restore an integrable majorant.
- `concrete_example_against_one`: fully explicit deterministic nonvacuity; the comparison one is not claimed to be a rough-Heston transform.

All appear in formal/RoughHeston/*.lean and passed the clean check recorded in VERIFICATION.md. The algebraic theorems actually allow every alpha>0; their rough-Heston interpretation is restricted to alpha in (1/2,1). The packaged nonintegrability theorem fixes R=-2, K=1 and zero drift, while the exponent theorem is broader. This specialization is explicit, not a claim to have checked every parameter version of the informal argument.

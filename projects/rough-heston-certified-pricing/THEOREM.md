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

For M0>=1, M_l=2^l M0 and delta_l=T/M_l. The requested domination is D_R(u)=sup_l delta_l^(-pG)|P-hat(u+iR)||Phi(u+iR)-Phi_(M_l)(u+iR)|, pG=min(q,rT). Neither q nor rT is assigned an empirical value in this project.

## Deterministic theorem and exact checked scope

For every alpha in (1/2,1), real R,rho,theta,X0,r, positive gamma,nu,V0,T, and integer M>=1, the above polynomial recurrence has deg_u h_M=4^M with positive real leading coefficient L_M. Write c=(gamma nu)^2/2, b=delta^alpha/Gamma(alpha+1), a=delta^alpha/Gamma(alpha+2). Then L_1=a c b^2/4 and L_(n+1)=a c^3 b^2 L_n^4. The real part of G_M has degree 2*4^M and leading coefficient delta V0 c L_M^2/2>0. Consequently no fixed M can make the discrete transform globally bounded on a horizontal contour.

The checked analytic consequence specializes to K=1, R=-2, S0=1, r=0: against any globally bounded comparison function Phi:R→C, the modulus error multiplied by the genuine call transform is not integrable on (0,infinity). The true payoff integral identity is also checked. The concrete all-level supremum has infinite extended Lebesgue integral for every real normalization exponent p, and no integrable majorant exists even after removing any fixed number of levels. No empirical convergence order is used. This does not establish the moment domain, pointwise convergence rates, stochastic model identity, or every premise of the conditional conjecture.

A concrete nondegenerate algebraic example is H=1/4, gamma=nu=theta=V0=T=S0=K=1, rho=-1/2, r=0, R=-2. These satisfy the listed numerical parameter inequalities. The literature establishes moment admissibility for this example (see MANUSCRIPT.md); the stochastic moment bridge is NOT presently Lean-checked.

## Unresolved repair and financial objective

For this unchanged PECE recurrence, removing a fixed number of coarse levels cannot repair an obstruction that holds for every finite M. Repairs may change the solver, couple the mesh to frequency, or truncate the Fourier domain with a certified exact tail. A pricing theorem still needs proved q,rT, constants, moment admissibility, stochastic model-to-transform identity, payoff integral, Fourier inversion, and quadrature error. No VIX extension is claimed.

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

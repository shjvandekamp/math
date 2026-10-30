# Implementation audit — 2026-10-15

The 2026 source specifies composite trapezoidal integration of J=theta gamma h+V0 F in Eqs. (11)–(13). The exact single-correction Adams weights in THEOREM.md are reconstructed from El Euch–Rosenbaum, arXiv:1609.02108v1, §5.1, Eqs. (26)–(27). Its final displayed formula has a dangling t_j in a predictor argument; the preceding predictor construction identifies the new endpoint t_(n+1).

The main paper does not print predictor weights/correction count, and its own source code was not found. Consequently the theorem concerns an explicitly defined standard reference scheme paired with the published exponent. It is an implementation extension/obstruction, not byte-level verification of the authors' executable.

## Public benchmark code is different

Inspected [SimonBreneis repository, commit 985ef2b66ff75535965cf91361b56083819bef69](https://github.com/SimonBreneis/approximations_to_fractional_stochastic_volterra_equations/blob/985ef2b66ff75535965cf91361b56083819bef69/rHestonFourier.py). This is cited for the BL2 Markovian benchmark, not identified as the authors' main Adams code.

Lines 31–46 use a predictor equal to the corrector history sum plus the endpoint coefficient times F(h_n), then one correction. Lines 47–50 retry at roughly 1.3M nodes if a solution exceeds 10^70. That adaptive wrapper is not a globally fixed-M polynomial. Lines 102–114 transform Fourier input and trapezoidally integrate h and h²; lambda=gamma, nu_code=gamma nu, theta_code=gamma theta recovers the target exponent.

The fixed-M branch has the same degree mechanism, but its coefficient recurrence differs. Its adaptive retry behavior needs a separate proof and is outside the formal theorem.

## Mechanism being verified

Let c=(gamma nu)^2/2, a=delta^alpha/Gamma(alpha+2), b=delta^alpha/Gamma(alpha+1). At the first step the predictor's leading coefficient is -b/2 and its square yields L1=a c b²/4. At later steps only the latest history value has maximal degree: prediction and correction each double degree, so L_(n+1)=a b² c³ L_n^4 and deg h_n=4^n. The final trapezoid endpoint then uniquely determines the exponent's positive leading coefficient delta V0 c L_M²/2.

This exact-arithmetic claim concerns every finite mesh, not overflow or a numerical fit. It does not establish moment admissibility, convergence rates, or nonintegrability of the real-part pricing integrand.

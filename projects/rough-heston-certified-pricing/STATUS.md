# Status — 2026-10-15

**Incomplete pricing project. The global deterministic Riccati construction, actual Adams convergence rates, Fourier domination obstruction and cutoff repair are now proved. Stochastic pricing identification remains open.**

## Current deterministic result

For gamma=nu=theta=V0=1, rho=-1/2, R=-2, every finite T>0 and 1/2<alpha<1:

- The actual fractional Riccati equation has a constructed solution family for every real frequency. Re h<1 and an explicit norm bound hold on every finite frequency band. No existence, derivative, regularity or invariant-region hypothesis remains in this concrete construction.
- The exact deterministic exponential Phi=exp(G) is globally bounded by B=exp(T+T^(1-alpha)/Gamma(2-alpha)). Its genuine strike-one call-weighted Fourier integrand is absolutely integrable.
- The actual one-predictor/one-corrector fractional Adams recurrence has derived conservative rates q=rT=alpha. The nodal bound has the source's t^(alpha-1) factor; the pure trapezoid estimate uses exact-node values. Every original level of every positive prescribed M0 is included, with frequency-dependent constants.
- Every finite mesh still has polynomial degree 4^M in its final node and positive leading real exponent coefficient of degree 2*4^M. Against this constructed exact deterministic Phi, the all-original-level domination function at pG=alpha has infinite integral. Removing a fixed number of levels cannot fix it.
- For every cutoff U>0, one validated seed gives every-refinement cutoff/time error <=U*Cphi*delta^alpha/2+B/U for the actual deterministic Fourier integrals. Cphi and a sufficient positive mesh threshold are explicit real expressions. Frequency continuity and integrability are proved, not assumed.

The general-coefficient finite-band theorem still assumes an actual bounded exact family. The concrete coefficients above discharge that assumption globally. Local existence/uniqueness and the earlier explicit short-maturity example are retained as separately checked results.

The clean ./verify.sh run exited 0 after rebuilding 40 modules including the library entrypoint and checking 43 headline axiom dependencies. Every audited list contains only propext, Classical.choice and Quot.sound. Peak process-tree RSS was 1,512,816 KiB (about 1.44 GiB). See VERIFICATION.md and certificates/. The source-convention and integrability findings from independent review are resolved.

## What the proof actually uses

Actual Gamma weights and cell integrals -> Holder consistency including zero -> exponential full-history row estimates -> validated predictor/corrector induction -> explicit mesh threshold -> actual trapezoid/exponential error. Coarse errors are absorbed only at fixed frequency, without claiming their constants are integrable in frequency.

For global existence: actual fractional semigroup/Fubini -> local little-Holder regularity -> backward-difference maximum principle -> first-contact invariant bounds. A continuous square cutoff makes the force globally Lipschitz; an exponentially rescaled path-space contraction solves the full-history equation for any finite T. The invariant bound proves the cutoff never activates. The family is selected for each finite maturity, not asserted jointly consistent across all maturities.

## Scope and novelty

The source algorithm is reconstructed from the primary El Euch–Rosenbaum reference. The main authors' executable was not found. The public BL2 benchmark uses a different predictor/retry wrapper and was not substituted. This remains a reference-scheme extension, not byte-level certification of unavailable author code.

General Adams instability and the analytic tools used in the repair are known. No matching public resolution found as of 2026-10-15 for the precise all-finite-mesh polynomial mechanism and domination consequence in the searches performed; novelty remains provisional. The new construction closes the deterministic bounded-comparison and rate gaps, but not the source's stochastic moment-domain premise. Do not advertise a fully admissible financial counterexample or complete option-pricing theorem.

## Remaining obligations

1. Construct the rough-Heston stochastic Volterra model, with nonnegative variance and correlated Brownian drivers, in the checked dependency chain.
2. Prove its affine transform and moment identities and R=-2 admissibility. The deterministic exponential bound is not a proof of a probabilistic moment identity.
3. Prove the Fourier expectation/pricing inversion with the correct normalization and discounting.
4. Evaluate the real mesh/cutoff certificates and prove numerical quadrature and floating-point/enclosure error, then assemble the final option-price inequality. The current repair leaves the finite Fourier integral as an exact integral.

## Next executable step

Audit and locally validate compatibility of formal-mathfin's actual predictable-L2 Ito integral APIs at pinned commit f1a3f3779bb4468af255594dbf270ae91cece443. See formal/INFRASTRUCTURE.md for inspected declarations, versions and limits. Its environment is Lean 4.33.0-rc1 with different Mathlib/BrownianMotion pins, while this proof project uses Lean 4.34.1. Do not change this project's verified pins or count source inspection as a checked import.

The next nonduplicate mathematical target is the singular stochastic convolution Z_t=integral_0^t K_alpha(t-s)*theta_s dW_s for bounded predictable theta: use the existing proved continuous linear Ito operator, derive its exact L2 energy and kernel increment bounds for alpha>1/2, then obtain a continuous process representative. Do not rebuild elementary Ito isometry merely because it is absent from this Mathlib snapshot. Square-root Volterra existence, joint-filtration integration and the affine identity remain subsequent substantial work.

## Failed or insufficient routes

- Fixed refinement cannot repair the global tail; every finite M is obstructed.
- Overflow and plotted slopes are not proof; neither is used in the formal result.
- A short-time supnorm contraction alone cannot give fixed-maturity pricing accuracy. Full-history weighted continuation and the global cutoff construction now replace that limitation.
- Ordinary alpha-Holder continuity alone is insufficient for the fractional extremum argument. The local little-Holder improvement was derived explicitly.
- An integral-of-difference bound alone could hide nonintegrability because Lean totalizes integrals. Exact-transform continuity and both band integrability facts are now derived before comparing actual integrals.
- Total numerical exponent error is distinct from the source's exact-node trapezoid premise. Both are proved separately.
- A theorem called Ito formula or SDE existence is not automatically a rough-Heston bridge. External declarations and their hypotheses must be inspected; named badges and agent agreement are not evidence.

## Workspace and verification discipline

Worktree: /Volumes/2tb/math/.worktrees/rough-heston-certified-pricing-20261015. Branch: research/rough-heston-certified-pricing-20261015. All changes remain inside projects/rough-heston-certified-pricing. One low-priority, single-threaded Lean process at a time; the shared wrapper enforces a 2 GiB process-tree RSS limit. Run ./verify.sh for the clean project build and axiom audit.

This deterministic research checkpoint is prepared for the user-authorized GitHub upload, including the remaining obligations and next executable step above. No trading, author contact, purchase or automation was performed. This checkpoint does not imply work continues after the active session.

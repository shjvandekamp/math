# Status — 2026-10-15

**Incomplete research project. A substantial deterministic reference-scheme theorem is fully Lean-checked; the requested end-to-end pricing objective is not complete.**

## Verified result

For every finite positive mesh of the explicit standard single-correction fractional-Adams scheme, the final node has degree 4^M and the published trapezoidal exponent has degree 2·4^M with positive real leading coefficient. For the genuine strike-one call on R=-2, zero drift, the modulus error against any bounded comparison transform is nonintegrable. The normalized supremum over all dyadic levels has infinite integral for every real exponent p. Removing finitely many levels cannot restore an integrable majorant.

The concrete weights and recurrence, tail argument, payoff integral, supremum, and deterministic nonvacuity instance are checked. `./verify.sh` exited 0. Headline axiom dependencies are exactly propext, Classical.choice and Quot.sound. See VERIFICATION.md and certificates/.

## Scope and novelty

The source algorithm is explicitly reconstructed from the primary reference. The main authors' executable was not found. The cited public BL2 benchmark repository uses a different predictor and an adaptive retry wrapper; it is not silently substituted. This is an implementation extension/obstruction, not a byte-level certification of author code.

Adams instability is known. No matching public resolution found as of 2026-10-15 for the precise all-finite-mesh polynomial mechanism and this domination consequence in the searches performed; novelty remains provisional. The conditional conjecture's full antecedents have not been established.

## Remaining mathematical obligations

1. Derive fixed-frequency q and exponent-integration rT for the actual fractional Riccati solution, treating the t=0 singularity. The current negative theorem works for every p but does not prove that either convergence rate exists.
2. Establish a useful repair at fixed maturity and arbitrary accuracy. The manuscript's finite-band contraction estimate requires a short horizon that worsens with the cutoff U; it does not solve this requirement. Validated continuation or a different stable solver needs a proof.
3. Formalize the rough-Heston stochastic model, its affine transform and moment identity, and prove the R=-2 contour admissible for the concrete rho=-1/2 example. The literature gives an on-paper bounded moment, not a Lean bridge.
4. Complete Fourier inversion, quadrature, truncation, rounding, and the final price-error inequality.

## Next executable research step

Start from the checked project with `./verify.sh`. For the analytic continuation, formalize positivity and row sums of the full Adams weights, then the finite-band Hölder consistency argument in MANUSCRIPT.md in a new `formal/RoughHeston/FiniteBand.lean`. Do not claim a global repair from the local contraction condition: the next substantive missing lemma is a validated continuation/discrete fractional-Gronwall estimate on a fixed maturity interval. Separately, an admissible moment bridge must connect an actual stochastic process to the bounded comparison in Main.lean.

## Failed or insufficient approaches already recorded

- A fixed refinement threshold cannot cure the global tail: the checked obstruction holds at every finite M.
- Floating-point overflow and finite numerical plateaus are not nonintegrability evidence; only the analytic lower bound is used in Lean. discovery/numerical_probe.json contains illustrative samples only.
- A global sup-norm contraction over [0,U] becomes restrictive as U grows; it cannot alone give arbitrary-tolerance pricing at fixed T.
- Legacy Lean imports exceeded the memory budget. Lean module mode, private tactic imports and serialized direct compiler calls brought the final peak below 1.5 GiB. No further broad rebuild is needed absent a source change.

## Workspace and integration

Repository origin: https://github.com/shjvandekamp/math.git. Base commit: 7566886. Worktree: /Volumes/2tb/math/.worktrees/rough-heston-certified-pricing-20261015. Branch: research/rough-heston-certified-pricing-20261015. All project work is confined to projects/rough-heston-certified-pricing. Other research worktrees and the root checkout's unrelated .DS_Store were preserved.

No remote push, publication, trading, author contact, purchase, or future automation was performed. This file is a checkpoint; it does not imply work continues after the active session.

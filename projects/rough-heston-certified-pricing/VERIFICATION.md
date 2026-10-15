# Verification — 2026-10-15

## Result

`./verify.sh` completed with **exit status 0** after clearing this project's generated outputs. It rebuilt 40 modules including the public library entrypoint, in their actual local dependency order, then ran AxiomAudit for 43 headline declarations. One pre-existing tactic-style linter warning remains in Adams.lean; there are no proof errors.

Compiler: Lean 4.34.1, arm64-apple-darwin24.6.0, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release. Mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612. Transitive revisions remain pinned in formal/lake-manifest.json.

## Checked headline and scope

`exists_concrete_deterministic_obstruction` constructs an actual global Riccati solution family for the concrete coefficients, derives the source's nodal and pure exact-node trapezoidal rates q=rT=alpha on every original dyadic level, proves a global exponential bound, and proves the domination function at pG=alpha has infinite integral for every original positive base mesh. Its rough range is 1/2<alpha<1, with arbitrary finite T>0. No bounded comparison, existence, invariant region or regularity premise is left in this concrete theorem.

`exists_concrete_deterministic_cutoff` constructs an actual family, proves absolute integrability of its genuine strike-one call Fourier integrand, and proves the cutoff/time error bound U*Cphi*delta^alpha/2+B/U on all refinements of a validated seed for each U>0. Measurability and integrability are derived from the equation and uniform approximation. It leaves the finite Fourier integral unevaluated.

These statements are deterministic. The exponential is not identified with a rough-Heston probability transform, and the integral is not identified with an expected discounted payoff. The earlier general-coefficient tail obstruction and finite-band approximation theorems remain available with their explicit hypotheses. The new concrete construction uses gamma=nu=theta=V0=1, rho=-1/2, R=-2 and zero affine drift. Separate phase identities cover the exp(-R*m) scaling; the assembled concrete cutoff statement does not insert drift or discounting.

## Dependency evidence

`certificates/axioms.txt` contains the actual `#print axioms` output for 43 declarations, including both new constructed headline theorems, global existence, invariant bounds, actual weight/consistency estimates, original-level rates, exact-node quadrature, semigroup/Fubini, frequency continuity and actual Fourier integrability. All lists contain only:

```text
propext, Classical.choice, Quot.sound
```

There is no sorry, admit, sorryAx, substantive new axiom, unsafe proof, native_decide, external oracle or solver field assuming the desired conclusion in the project sources. `ConcreteSourceRates` is an explicit proposition proved as a conclusion about the actual recurrence; it is not supplied as an assumption. The generic preliminary estimates retain their stated hypotheses, which the concrete chain discharges.

## Reproduction and resources

From the project root run `./verify.sh`. It selects the existing pinned runtime on this Mac, or relies on an appropriate elan environment elsewhere; verifies Mathlib HEAD; scans for forbidden proof constructs; derives the project import order from formal/RoughHeston.lean; rebuilds the reachable proof modules and entrypoint; and records the axiom audit. It deletes only this project's generated outputs. The generated module list is formal/.lake/build/project-modules.txt.

Each compiler call goes through `bounded_lean.py`: nice level 19, one Lean thread, a shared compilation lock and a 2 GiB process-tree RSS limit. The largest process-tree peak in the complete successful run was **1,512,816 KiB (about 1.44 GiB)**. Dependencies are isolated APFS copies. Targeted cache additions supplied the Beta/Gamma and fixed-point dependencies; pinned revisions did not change.

Evidence is in certificates/clean-build.log, certificates/axioms.txt and certificates/toolchain.txt. Numerical discovery output is illustrative and is not used as a certificate.

## Independent statement audit

STATEMENT_AUDIT.md records the independent reviews. Two material integration findings were resolved: the actual band-integral theorem now proves integrability rather than only bounding a totalized integral of a difference; and the source's exact-node time-integration premise is proved separately from total numerical exponent error, with strictly positive source constants. The global first-contact proof retains full history, the cutoff image bound is 2Q, and no derivative of the fractional solution is assumed.

Review agreement is not a proof. The compiled declarations, their dependency closures and the inspected quantifiers are the evidence.

## Not checked as a financial theorem

Still outside the dependency chain: stochastic rough-Heston model existence/nonnegative variance, correlated-driver filtration integration, affine transform and moment identities, R=-2 moment admissibility, Fourier pricing inversion, evaluated numerical mesh/cutoff certificates, quadrature, rounding and the final option-price error. The authors' unavailable executable is not certified; the recurrence is the explicitly reconstructed standard single-correction reference scheme.

The external mathfin source audit in formal/INFRASTRUCTURE.md identifies useful Ito integration infrastructure, but those sources were neither imported nor kernel-checked in this environment. Their different toolchain and dependency pins require an isolated compatibility audit. No complete financial counterexample, completed pricing project or VIX extension is claimed.

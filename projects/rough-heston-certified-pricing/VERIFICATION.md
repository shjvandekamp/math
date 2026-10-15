# Verification — 2026-10-15

## Result

`./verify.sh` completed with **exit status 0** after clearing and rebuilding this project's generated proof modules. It compiled Weights, Adams, Exponent, Tail, Payoff and Main in dependency order, then ran AxiomAudit. One harmless tactic-style linter warning remains in Adams.lean; there are no proof errors.

Actual compiler: Lean 4.34.1, arm64-apple-darwin24.6.0, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release. Mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612. All transitive revisions are pinned in formal/lake-manifest.json.

## Checked claims

The combined theorem is a deterministic all-finite-mesh obstruction for the explicit reference PECE recurrence. Concrete Gamma weights, recurrence evaluation identities, exact polynomial degrees, positive leading exponent coefficient, the actual vanilla-call Fourier integral at K=1/R=-2, analytic nonintegrability, dyadic levels and the extended-real supremum are checked. Main's packaged tail theorems use zero drift; Exponent also checks arbitrary affine drift and real contour parameter.

`certificates/axioms.txt` records the full `#print axioms` output for 13 declarations, including `reference_genuine_call_not_integrable`, `domination_lintegral_eq_top`, `no_integrable_majorant_after_fixed_level`, and both explicit example declarations. Every list contains only:

```text
propext, Classical.choice, Quot.sound
```

No sorry, admit, sorryAx, new axiom, unsafe proof, native_decide, numerical oracle, or structure field assuming the desired conclusion occurs in the project proof sources. The generic bound on the comparison function is an explicit hypothesis of the deterministic theorem, not a claimed derivation of the model transform.

## Reproduction and resource behavior

From the project root run `./verify.sh`. On this Mac it selects the existing pinned runtime under /Volumes/2tb/math/.research-cache/toolchains. On another machine, an installed elan/Lake environment must supply the version in lean-toolchain. Missing dependencies are restored with Lake and the official Mathlib cache. The script checks Mathlib HEAD, rejects forbidden proof constructs, rebuilds project outputs, and records the compiler identity, clean log and axiom output.

Proof commands use `python3 bounded_lean.py -o .lake/build/lib/lean/RoughHeston/<Module>.olean RoughHeston/<Module>.lean`; the wrapper resolves LEAN_PATH, then invokes `nice -n 19 lean -j1`, serialized by a project-local lock. It monitors only its own child process tree and stops that job above 2 GiB RSS. The largest compiler-tree peak in the successful clean run was 1,474,240 KiB (about 1.41 GiB). Dependencies are isolated APFS copies, not writable links to other research projects.

## Independent statement audit

See STATEMENT_AUDIT.md. The independent reviewer checked the informal/formal quantifiers, concrete weights and endpoints, one-correction algorithm, bounded-comparison qualification, true rational call factor, all-level supremum, and distinction between modulus and real-part errors. Its actionable scope/documentation findings were resolved. The primary agent also reviewed the delegated proof code and the additional payoff integral proof. Agent agreement is not proof; successful kernel checks and the inspected statements provide the formal evidence.

## What this does not verify

The authors' unpublished executable, floating-point rounding, stochastic rough-Heston existence, model-to-transform identity, moment admissibility, Fourier pricing inversion, full nodal/time-integration rates q and rT, a globally justified repair, quadrature and final option-price error are not in this dependency chain. The nondegenerate moment example in MANUSCRIPT.md uses external literature. No financial completion or fully established conditional-conjecture counterexample is claimed.

# Verification evidence and reproduction

**Both main theorems passed compilation, axiom inspection, independent
compiled-statement audit, and a clean rebuild of their project source closure.**
The finite and structural clean runs each exited zero. All verification jobs
are finished.

## Pinned environment

- Lean `leanprover/lean4:v4.34.1`, runtime commit
  `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Transitive revisions: [formal/lake-manifest.json](formal/lake-manifest.json).
- Repository base: `fe3e100fa673a64037771e42d95b7718379a29bd`.
- Python 3.9 or later; the exploration and certificate generators use only the
  standard library. The conic nullspace check uses `math.lcm`. Git is needed
  for dependency revision checks.

## Reproduce

Install the pinned Lean toolchain. On a fresh machine, materialize the saved
dependency manifest and obtain the matching dependency artifacts first:

```sh
export PATH="/path/to/lean-4.34.1/bin:$PATH"
cd formal
lake resolve-deps
lake exe cache get
cd ..
./verify.sh --clean
```

The bootstrap requires network access. `lake resolve-deps` uses the committed
manifest; `lake update` is not the reproduction command because it updates
dependency resolutions. The verifiers intentionally reject missing, modified,
or incorrectly pinned dependency checkouts. They recompile project sources,
while retaining the pinned dependencies' compiled cache.

The ordinary cache bootstrap above may use parallel decompression. It is
outside the source verifiers' single-thread resource guarantee. On the
constrained development host, required missing artifacts were downloaded with
`cache get-` and extracted with `leantar --jobs 1`; an ordinary parallel cache
bootstrap was not run under that host's one-job allowance. Fresh-machine
bootstrap was checked against the pinned Lake and Mathlib implementation,
but a second complete dependency download was not performed.

With dependencies already present, the one-command entry point is:

```sh
LEAN_BIN=/path/to/lean-4.34.1/bin ./verify.sh --clean
```

It runs `verify-finite.sh --clean` and then `verify-structural.sh`, sequentially.
The finite clean phase removes `formal/.lake/build`, rebuilds its whole project
closure, and audits the finite statement. The structural phase then recompiles
its whole project closure and audits the structural statement. Individual
component commands are also available:

```sh
LEAN_BIN=/path/to/lean-4.34.1/bin ./verify-finite.sh --clean
LEAN_BIN=/path/to/lean-4.34.1/bin ./verify-structural.sh --clean
```

Standalone structural cleaning removes only the outputs of its 24-module
project closure; it preserves the separate finite certificate outputs. The
shared foundations are recompiled. All compiler invocations are synchronous,
`nice -n 19`, `-j 1`, and `-M 2500`; Lake resolves the environment once and exits
before compilation. `LEAN_MEMORY_MB` permits an explicit alternative cap.
The thread-related numerical-library environment variables are set to one.

## Successful runs

| Target | Source rebuild evidence | Axiom evidence | Independent statement audit |
|---|---|---|---|
| Four-period source basis | [finite-clean-build.log](formal/finite-clean-build.log), 72 project modules, exit 0 | [main-axioms.txt](formal/main-axioms.txt), 13 declarations | [FINITE_STATEMENT_AUDIT.md](reviews/FINITE_STATEMENT_AUDIT.md), PASS |
| Arbitrary-period dimension | [structural-clean-build.log](formal/structural-clean-build.log), 24 project modules, exit 0 | [structural-axioms.txt](formal/structural-axioms.txt), 12 declarations | [STRUCTURAL_STATEMENT_AUDIT.md](reviews/STRUCTURAL_STATEMENT_AUDIT.md), PASS |

The finite run used the former finite-only `./verify.sh --clean`; that exact
finite workflow is now `verify-finite.sh` (only its usage text changed).
The structural run used `./verify-structural.sh --clean` after deleting all
outputs in its project closure. The combined wrapper was syntax checked and
independently reviewed; the two successful component runs were not repeated
as one combined invocation. No Lean theorem sources changed after these runs.

The finite verifier regenerated the exact coefficient/minor certificate and
compared it byte for byte with the saved data. It checked all generated Lean
files, then compiled the primitives, 39 scalar proof chunks and final theorem.
The structural verifier compiled the graded algebra, explicit separators,
block induction, actual likelihood bridge, economic genericity, and final
dimension theorem. Both checked dependency revisions and tracked changes,
printed fresh theorem types and axiom output, and rejected forbidden proof
constructs throughout the project proof sources.

## Trust and statement checks

The active source-family continuation has a separate, smaller verifier:

```sh
LEAN_BIN=/path/to/lean-4.34.1/bin ./verify-source-family.sh --clean
```

It checks the exact general family, universal moment validity, exact source
recursion, the cardinality and empty/singleton parameterization of the actual
indices, the conditional-tail induction criterion, and its joint-image
equivalence. It checks the actual source joint-image normalization and the
empty/singleton matrix-product formulas through proved finite Markov marginals,
including their exact selected-first, ascending-remainder block orders.
It checks the reversible empty-column replacement, normalization and
reindexing of the actual new images, and the resulting conditional criterion
in terms of the reduced columns.
It also checks the auxiliary binary identities and constant-real
span parity/baseline theorems, polynomial endpoint separation, paired-defect
independence, and the rank formula for the actual move-first binary words.
It also checks the exact stochastic-matrix identities and transfers their rank to functions
on the positive domain through injective restriction and determinant scaling.
It does not discharge the criterion's new-image independence hypothesis,
prove the new polar theorem, or validate the external rank certificates.
The source-foundation and recursion statement reviews are in
[SOURCE24_FOUNDATIONS_AUDIT.md](reviews/SOURCE24_FOUNDATIONS_AUDIT.md) and
[SOURCE24_RECURSION_AUDIT.md](reviews/SOURCE24_RECURSION_AUDIT.md).
The original two-theorem `verify.sh` entry point is unchanged.

The continuation verifier passed its clean 24-module rebuild and all
220 axiom checks with exit zero. Evidence:
[source-family-clean-build.log](formal/source-family-clean-build.log) and
[source-family-axioms.txt](formal/source-family-axioms.txt). The only diagnostic
was an existing stylistic linter warning in `BasisCertificate.lean`.

The subsequent six modules passed focused source compilation and add 95
axiom checks, without warnings in the final runs. They include the actual
binary matrix rank, the actual three-state homogeneous representation,
and polynomial clearing with the equivalent conditional induction criterion.
The extended aggregate checks all 315 requested declarations against the
compiled 30-module closure; its
output is [source-family-extended-axioms.txt](formal/source-family-extended-axioms.txt).
The reproducible verifier now includes all six new modules. This extended check
reuses the earlier compiled closure; it is not a new clean 30-module rebuild.
The audited deletion-word induction remains a paper proof whose k=4 base
is the external certificate in `exploration/source24-deletion-word-results.json`;
it is not covered by the Lean verifier.

Every audited declaration in both main checks depends only on
`propext`, `Classical.choice`, and `Quot.sound`. There are no `sorry`, `admit`,
`sorryAx`, custom axioms, or native computation oracles in the project proof
sources. Generated numeric data are untrusted inputs until their formula and
right-inverse identities are checked by the kernel; every such finite
certificate used in the theorem passed.

The independent finite audit maps the 33 source indices, 81 paths, all three
initial states, positive-effect quantifier, economic normalizations, column
scaling, explicit minors and actual moment space. The independent structural
audit maps the unrestricted-effect moment space, positive path amplitudes,
fixed-degree dehomogenization, closed interpolation induction, natural-number
arithmetic, parameter domain, and explicit nonvacuous generic region. Neither
audit establishes publication priority or general-period source-family
independence. Their full reports retain the review-time context.

The external exact certificate SHA256 is
`1f314f167910b7d9a65e3567ddda625a6f6b8a839e79ffe0cdf84385c8945ca5`.
The earlier coefficient minor is discovery evidence; the formal finite proof
uses independently kernel-checked evaluation minors and modular inverse
certificates. See [exploration/LOG.md](exploration/LOG.md).

## Earlier resource failures and narrower checks

An earlier monolithic Witness attempt was stopped after exceeding the host's
resource allowance. A separate early interpolation attempt with a 768 MiB
Lean cap failed before source diagnostics. Neither failed attempt is used as
acceptance evidence. The replacement certificate chunks and repaired
interpolation modules passed the final source rebuilds above.

The host eventually allowed one single-threaded job under a 2.5 GiB aggregate
ceiling. The successful finite assembly used a 2500 MiB Lean cap, with maximum
RSS 2,513,960,960 bytes and footprint 410,324,096 bytes. MainCheck succeeded
with maximum RSS 2,379,530,240 bytes. RSS and footprint are distinct metrics.
No increase beyond the host's allowance was made by this project.

`formal/verify-foundations.sh` and `formal/foundation-axioms.txt` retain the
older four-module foundation check. That narrower check is superseded for
main-theorem acceptance by the two complete source rebuilds above.

The residue-difference paper identities R1–R18 passed independent statement
review. The new `source24_residue_differences.py` run checks their operator
and seed-decomposition formulas at m=3 and m=5, including actual OY=Z
solves and the projected incoming equation OY0=z0. It completed in 1.12
seconds with 20.6 MiB maximum RSS. This external modular diagnostic is
separate from the Lean checks and proves no uniform transversality claim.

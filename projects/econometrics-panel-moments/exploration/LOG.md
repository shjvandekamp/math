# Exact exploration log

15 October 2026. The first bounded source audit preceded matrix computation.
Machine has 16 GiB RAM and substantial existing memory pressure; this project
uses no more than two concurrent heavy local processes.

`exact_q3t4.py` uses only Python standard-library integers. It builds the
source numerator matrix K, scaled coefficient matrix C0, 18 base points and
degree-10 separating evaluations directly from model primitives. Modular
elimination selects minors; Bareiss integer elimination then computes their
actual integer determinants and checks every division has zero remainder.
No floating point rank threshold is used.

First candidate: g=[[1,1,1],[1,2,3],[1,5,7]], period multipliers
(1,2^t,3^t). A separator diagonal vanished, so this candidate did not certify
the required geometric nonincidence conditions. It was not interpreted as a
counterexample to any generic claim.

Successful candidate: g_qr=2^(qr), pi_tqr=2^(q(3t+r)), using q,r=0,1,2 and
t=1,2,3,4. This is the normalized scalar-covariate economic witness in
THEOREM.md. Exact output:

- 81 paths, 33 indexed source moments, 66 monomial coefficients;
- nonzero 48-by-48 C0 minor, determinant has 980 signed decimal characters;
- nonzero 33-by-33 K minors for all three initial states;
- C0 K^T=0 exactly for each initial state;
- 18 independent evaluation rows, witnessed by a diagonal separator matrix;
- evaluation matrix E satisfies E C0=0 exactly.

Certificate SHA256:
`1f314f167910b7d9a65e3567ddda625a6f6b8a839e79ffe0cdf84385c8945ca5`.
Full matrices, fixed minor indices and exact determinants are retained in
`q3t4-certificate.json`. Regenerate with
`python3 exploration/exact_q3t4.py --output exploration/q3t4-certificate.json`.

These are reproducible external exact computations. They have **not yet**
been turned into Lean kernel-checked determinant/rank certificates. Exact
arithmetic alone does not meet the project's formal acceptance criterion.


## Continuation: exact equation-(24) checks for T >= 5

15 October 2026. `general_source24.py` adds the nonvacuous footnote-8 shared
prefix restriction while preserving the old T4 script and certificate.
Its T4 indices and all integer entries agree exactly with the old generator.
The new runs are external discovery evidence, not Lean-verified certificates.

| Witness transition G[2,2] | T | Prescribed rows | Modular rank | Lifted rank | Added quotient rank |
|---|---:|---:|---:|---:|---:|
| 16 (original) | 4 | 33 | 33 | 9 | 24 |
| 16 (original) | 5 | 162 | 159 | 99 | 60 |
| 16 (original) | 6 | 606 | 597 | 477 | 120 |
| 17 (perturbed) | 5 | 162 | 162 | 99 | 63 |
| 17 (perturbed) | 6 | 606 | 606 | 486 | 120 |

All original checks and perturbed T5 used primes 1,000,003 and 1,000,033;
perturbed T6 used 1,000,003. Every initial-state matrix is compared entrywise
with the corresponding nonzero row scaling of the initial-zero matrix.
The saved JSON includes original-row/column minor indices and nonzero
modular determinants. Deficient modular ranks do not prove deficient real
rank; the full minors establish exact rank lower bounds conditional on the
external calculation. The perturbation is gamma[2,2]=log(17), with all other
normalized parameters, slopes (0,1,2), and covariates 3(t+1)log(2) unchanged.

Reproduction commands appear in the new script's header. The T6 perturbed
run took about 3.4 seconds and 20 MiB maximum RSS, single-threaded at nice19.
The old temporary host cap was lifted before this continuation; computation
remains bounded to avoid the host's observed memory pressure.

## Residue reduction for the continuation

`source24_residue.py` implements the double-pole matrix from
`research/SOURCE24_INDUCTION.md`. For each pair of lines from different
transition blocks, it evaluates the two residue coordinates using three-by-three
transfer products. It checks that the point has no zero coordinate, no third
denominator line passes through it, and the two residue vectors are independent.

For G[2,2]=17 and prime 1,000,003:

| T | Residue matrix size | Modular rank | Predicted added quotient rank |
|---|---:|---:|---:|
| 4 | 18 | 18 | 24 |
| 5 | 54 | 54 | 63 |
| 6 | 108 | 108 | 120 |
| 7 | 180 | 180 | 195 |
| 8 | 270 | 270 | 288 |

All six combinations of T=4,5,6 and G[2,2]=16,17 agree with the independently
computed path-quotient ranks. Every new-row formula agrees with direct path
sums at two finite-field effect points, and the single-block column operation
agrees there too. These sampled comparisons support the symbolic derivation;
they do not replace a proof of the rational identities.

A separate Gaussian-elimination implementation verifies the saved T5
162-square original source minor, obtaining determinant 360472 modulo
1,000,003. The residue scan also finds full T5 ranks for G[2,2] in
{5,9,15,17,18,25,36}, while G[2,2]=16 retains nullity three with irregular
time exponents {3,7,12,18,25}. Modular deficiencies remain insufficient to
deduce a real-rank upper bound.

Reproduce the saved `residue-results.json` with:

```sh
nice -n 19 python3 exploration/source24_residue.py \
  --scan-transition22 --irregular-conic \
  --output exploration/residue-results.json
```

The main run took 2.01 seconds and about 24.3 MiB maximum RSS. No exponential
path enumeration is performed for T=7,8. The all-T economic nonvanishing
argument and Lean certification of these finite computations remain open.

## Exact conic failure at T=5

`conic_residue_nullspace.py` subsequently resolved the real-rank question for
the original conic T5 residue matrix. It uses the original witness unchanged,
normalizes each cross-point to `(w*z, -w-z, 1)`, and records the first two
components of the zero-sum residue. This is an invertible change of residue
coordinates. Every geometry condition is checked over the rationals.

Three independent primitive integer nullvectors annihilate every row of the
original `Fraction` matrix exactly. A nonzero 51-square minor modulo
1,000,003 gives the matching lower bound, so its real rank is exactly 51.
The vectors have support sizes 16,16,20, use only shared and divergent labels
0 and 2, and have coefficients of at most 45 bits. The retained exact
identities provide an upper bound that a modular deficiency alone could not.

Under the paper-level quotient reduction this gives added rank 9+51=60,
short of the required 63. It rules out reusing that particular conic witness
for the source-independence induction. It does not contradict generic
independence or the separately proved structural dimension theorem.

```sh
nice -n 19 python3 exploration/conic_residue_nullspace.py \
  --output exploration/conic-nullspace-results.json
```

Runtime was 0.28 seconds with maximum RSS about 15.9 MiB. This is an external
exact certificate, not a Lean theorem; no full 162-row source-matrix
nullvectors are claimed in this file.

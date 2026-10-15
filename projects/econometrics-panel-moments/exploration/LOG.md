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

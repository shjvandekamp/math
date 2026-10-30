# Agent COL notes: the oldest–newest collision u_N = u_0 (20 Oct 2026)

Angle: collide the newest block N = n-1 with the oldest block 0, u_N = u_0 (1 + delta nu), delta -> 0
(Q = 3, product form). Question: can the bounded defect be turned into an induction?

Labels: **PROVED** (argument given here), **EXACT-CHECKED** (exact arithmetic mod p = 2^61-1 at random
product-form points; Smith exponents are computed over F_p[[delta]] with delta a formal variable, from
the ranks of block-Toeplitz matrices of exact jets; single random points, so evidence, not proof),
**CONJECTURE**, **REFUTED**.

Scripts (run from `exploration/` with `../../../.venv/bin/python <script>`; every script has a docstring
saying what it checks and what it does not show):

| script | content | runtime |
|---|---|---|
| `agent_col_lib.py` | jets mod p (truncated series in delta), term-list vectors, Laurent expansion along a doubled line, derivative block D; self-test vs `hq_fresh_coalesce.family_eval` | 1 s |
| `agent_col_defect.py` | task 1: Smith exponents at u_N = u_k | n=8: 6 s per run |
| `agent_col_s0.py` | delta=0 kernel, head/body form Q_cyc, append/prepend decomposition | 10 s (n<=6) |
| `agent_col_jets.py` | explicit jets, verification, double-pole separation | 30 s (n=5) |
| `agent_col_local12.py` | the 12 local functionals: vanishing on S_0, matrix on the jets | 20 s (n=5) |
| `agent_col_dpfun.py` | double-pole coefficients as exact rational functions on L_0c | 1 s |
| `agent_col_polar.py` | pole-order filtration of S_0 (ranks of dp, tau) | 1 min (n=5) |
| `agent_col_stepY.py` | Y = W_m + W_m K_0 inside S_0, new columns mod Y | 15 s |
| `agent_col_stepmap.py` | Y = A (+) Z, the delta=0 step map T0, head-map content | 10 s |
| `agent_col_zspan.py` | density of the Z-vectors in the cyclic family | 2 s |
| `agent_col_lambdaK.py` | candidate head-map transfer identity under K_0 | 4 s |
| `agent_col_latest.py` | latest-pair jets modulo the explicit space Y_lp | 7 s |
| `agent_col_iterated.py`, `agent_col_patterns.py` | iterated / periodic collisions | 30 s |
| `agent_col_cyclic.py` | cut points, reversed cycle, middle-order independence | 20 s (m<=5) |

## 0. Summary

* **Survived.**
  1. Bounded defect: exactly 12 for n = 5..9, Smith exponents only 0 and 1 (EXACT-CHECKED; 15 at n = 4).
  2. **Theorem C (PROVED, sec. 3.4):** the jet step is *local*. Twelve functionals supported at the six
     base points of block 0 (on the doubled lines L_0c) vanish on every delta = 0 family member and are
     independent on the 12 jets; their 12 x 12 matrix is block triangular with natural diagonal factors.
     Hence **P(n) <== Q_cyc(n-1)**: the 9m^2+12m-9 distinct delta = 0 members of the cyclic configuration
     (0, 1, ..., m-1, 0'), m = n-1, are linearly independent. Q_cyc(m) is EXACT-CHECKED for m = 4..8.
  3. Structure of S_0 (EXACT-CHECKED): the only delta = 0 relations are the 12 coincidences; S_0 contains
     the explicit space Y = W_m + W_m K_0 (dim W_m + 9m); S_0 = Y (+) (transverse double-pole part,
     dim 9(m-1), explicit); **S_0 does not depend on the order of the middle blocks** (an intrinsic space).
  4. Iterated collisions stay first-order clean, 12 per collision, as long as no block occurs 3 times.
* **Killed.** (a) A head-map-free step: the delta = 0 step contains a 9m x 9m map T0 whose old parts have
  dense, full-rank Lambda_m, the same size as the generic append step (also for the latest-pair variant).
  (b) as an induction: iterating does not remove Lambda; triple occurrences break cleanness. (c) rotation
  of the cut point: different cuts share only W_m. Also refuted: a transfer identity for Lambda under K_0,
  and S_0 = (nu-independent part of the flat limit).
* **Most promising next step:** sec. 6 (attack Q_cyc(m) through its intrinsic target space; the only
  non-explicit ingredient is the statement Z subset span(cyclic family), with Z an explicit 9m-dim space).

## 1. Setting

Blocks 0..N, N = n-1, m := n-1. u_N = u_0 (1 + delta nu), all other data generic. At delta = 0,
K_N = K_0 and the configuration is the *cyclic configuration* C_m = (0, 1, ..., m-1, 0'). Notation:
L_c := L_{0c}, v_c := (A_0(c,i) X_i)_i (so K_0(c,.) = v_c / L_c), L'_c := sum_i A_0(c,i) nu_i X_i,
ell_c := L'_c / L_c, V := diag(nu), Pi := K_1 ... K_{m-1}. On the line L_c: the boundary base point
z_c := L_c cap {X_c = 0} and the interior base points z_cd := L_c cap L_d (d != c).
For f with at most a double pole along L_c: dp_c(f) := (L_c^2 f)|_{L_c} (a zero-sum vector function on
L_c), tau_c(f) := dp_c(f) ^ v_c (pointwise wedge on the zero-sum plane).

## 2. Task 1: the defect is bounded (EXACT-CHECKED)

`agent_col_defect.py`, Smith exponents of the E/F evaluation matrix over F_p[[delta]] (K = 3, so
exponents 0, 1, 2, >2 are resolved), #fam/2 + 6 random evaluation points:

| n | k (u_N -> u_k) | seeds | exponents |
|---|---|---|---|
| 4 | 0 | 1, 2 | 0:105, 1:15 |
| 5 | 0, 1 | 1, 2 | 0:183, 1:12 |
| 6 | 0, 1, 2 | 1, 2 | 0:276, 1:12 |
| 7 | 0, 1, 3 | 1, 2 | 0:387, 1:12 |
| 8 | 0, 1, 4 | 1, 2 | 0:516, 1:12 |
| 9 | 0 | 1 | 0:663, 1:12 |

No exponent 2 or higher anywhere. (The brief's "0:274, 1:12" at n = 6 should read 0:276.) For
comparison k = N-2 gives 30 and k = N-1 gives 18n-24 (all exponents 0/1). Kill criterion not met.

**Coincidence count (PROVED, word comparison).** Equal words give equal vectors. For k <= N-3 exactly 12
pairs have equal (head, word): E_{N,a} = E_{k,a} and F_{N,k,a,b} = F_{k,N,a,b}; F_{t,N} vs F_{t,k} (and
F_{N,s} vs F_{k,s}) have equal words iff no block other than t (resp. s) lies strictly between k and N,
which adds 18 pairs for k = N-2 and 18(n-2) for k = N-1. That *no other* relation exists at delta = 0 is
EXACT-CHECKED (sec. 3.1), not proved.

## 3. Task 2: S_0, the jets, and a local reason

### 3.1 The delta = 0 kernel (EXACT-CHECKED)

`agent_col_s0.py (A)`: the left kernel of the delta = 0 family is exactly the span of the 12 pair
differences for n = 5, 6, 7 (and, via rank M_0 = |fam| - 12 in sec. 2, for n = 5..9). For n = 4 there
are 3 further relations, each involving E_{0,a}, all E_{1,.}, E_{2,.} and ~100 F's (dense), so the
reduction below starts at n = 5. Define

  **Q_cyc(m):** the 9m^2 + 12m - 9 vectors E_{s,a} (s < m), F_{t,s,a,b} (t != s < m), F_{t,N,a,b} (1 <= t < m),
  F_{N,s,a,b} (1 <= s < m), F_{0,N,a,b}, at u_N = u_0, are linearly independent.

EXACT-CHECKED for m = 4..8; false for m = 3.

**Head/body form (EXACT-CHECKED m = 4, 5, 6; same bookkeeping as AG 1.3).** Q_cyc(m) <=> the
9m^2 + 18m - 6 functions {h_tab : t < m} u {X_a e_a} u {bodies h_tab W_{t,s} at delta = 0, with the one
duplicate (N,0)/(0,N) removed} are independent (`agent_col_s0.py (B)`: ranks 210/210, 309/309, 426/426;
126/129 at m = 3).

### 3.2 The jets (PROVED + EXACT-CHECKED)

With D := dK_N/d delta at 0, D(a,i) = K_0(a,i)(nu_i - ell_a), differentiation gives

    JE_a  := d/d delta (E_{N,a} - E_{0,a})        = -X_a e_a D,
    JF_ab := d/d delta (F_{N,0,a,b} - F_{0,N,a,b}) = X_a D(a,b) e_b (I - K_0 Pi) + X_a K_0(a,b) e_b D Pi
           = X_a K_0(a,b) [ (nu_b - ell_a) e_b - (nu_b - ell_a + ell_b)(K_0 Pi)(b,.) + (K_0 V Pi)(b,.) ].

EXACT-CHECKED (`agent_col_jets.py`, n = 5, 6, 7): the formulas equal the delta-coefficients of the pair
differences; triple poles cancel; jets(nu) - jets(nu + (1,1,1)) lies in S_0 (nu matters mod (1,1,1));
rank of the jets modulo S_0 is 12. Only double poles occur, along the three lines L_c.

### 3.3 The double-pole data separate the jets (EXACT-CHECKED)

`agent_col_jets.py (4)`: rank dp(S_0 + jets) - rank dp(S_0) = 12 (n = 5, 6, 7); JE contributes 3, JF 9;
tau alone separates 9. `agent_col_dpfun.py` reconstructs dp_c as exact rational functions on L_c (n = 5,
line L_00): for every delta = 0 member, alpha_c (longitudinal part) vanishes to order >= 2 and tau_c to
order >= 3 at z_c, and nothing has a pole at z_01, z_02; JE_0 has alpha = X_0 L'_0 (order 1 at z_0),
JF_00 has tau of order exactly 2 at z_0, JF_01 has a pole at z_01.

### 3.4 Theorem C: the jet step is local (PROVED)

**Lemma 1.** For every delta = 0 family member f and every c: dp_c(f) = X_c^2 rho (v_c P) on L_c, with rho a
scalar and P a (possibly empty) product of kernels of blocks 1..m-1, both regular at z_c and z_cd.
*Proof.* A pole along L_c comes only from block 0: the head h_{0cb} = X_c v_c(b)/L_c e_b, or a factor K_0
entered in row c (K_0 = e_c v_c^T / L_c + regular). Block 0 occurs at most twice in head + word of a
delta = 0 member, so dp_c(f) is (scalar before the first c-pole) x (scalar between the poles) x v_c x
(suffix). Case list (R = the remaining middle blocks, a product of kernels of blocks >= 1):
(i) F_{t,s}, t,s >= 1, word s,0,R,0': dp_c = X_a K_t(a,b) K_s(b,c) (v_c R)(c) v_c;
(ii) F_{t,0}, word 0,R,0': X_a K_t(a,c) (v_c R)(c) v_c;  (iii) F_{t,N}, word 0,0,R (only b = c): X_a K_t(a,c) A_0(c,c) X_c v_c R;
(iv) F_{0,s}, head h_{0cb}, word s,R,0': X_c v_c(b) (K_s R)(b,c) v_c;  (v) F_{N,s}, word s,0,R:
X_c v_c(b) K_s(b,c) v_c R;  (vi) F_{0,N}: A_0(c,c) X_c^2 v_c R;  (vii) E: no double pole.
Each scalar factor contains X_c, a column-c entry of a kernel of a block >= 1 (proportional to X_c), or
v_c(c) = A_0(c,c) X_c; all factors are regular at z_c and z_cd (general position). ∎

**Consequences (PROVED).** On span(delta = 0 family) = S_0, for each c: (phi3) dp_c has no pole at z_cd;
(phi1) dp_c vanishes to order >= 2 at z_c; (phi2) tau_c vanishes to order >= 3 at z_c, because at z_c every
kernel of a block >= 1 has zero column c and v_c(z_c) has zero c-entry, so (v_c P)(z_c) and v_c(z_c) are
zero-sum vectors with zero c-entry, hence parallel.

**Lemma 2 (the 12 x 12 matrix).** Use the 12 functionals phi1_c = d/dtheta dp_c at z_c (3),
phi2_c = (1/2) d^2/dtheta^2 tau_c at z_c (3), and for each pair a < b the 2-vector Res_{z_ab} dp_a (6).
From the formula in 3.2:
* dp_a(JF_ab) = -X_a v_a(b) L'_a (e_b - (K_0 Pi)(b,.)) and dp_a(JF_ba) = -(X_b v_b(a)/L_b) L'_a v_a Pi on L_a;
  their residues at z_ab are X_a X_b L'_a / L_b' times A_0(a,b) v_b Pi and -A_0(b,a) v_a Pi; no other jet has a
  pole of dp_a at z_ab. The 2 x 2 block has determinant
  ~ A_0(a,b) A_0(b,a) (X_a X_b L'_a)^2(z_ab) det Pi(z_ab) (v_a ^ v_b)(z_ab).
* dp_c(JF_cc) = A_0(c,c) X_c^2 [v_c (V - nu_c) Pi - L'_c e_c]: phi1 = 0, and phi2 ~ A_0(c,c) L'_c(z_c) (the bracket
  has c-entry -L'_c(z_c) while v_c(z_c) has c-entry 0); dp_d(JF_cc) = 0 for d != c.
* dp_c(JE_c) = X_c L'_c v_c: phi1 ~ L'_c(z_c) v_c(z_c), tau = 0; dp_d(JE_c) = 0 for d != c.
Ordering rows (JF_ab | JF_cc | JE_c) and columns (residues | phi2 | phi1) gives a block upper-triangular
matrix, so

    det = prod_{a<b} [A_0(a,b) A_0(b,a) (X_a X_b L'_a)^2 det Pi (v_a ^ v_b)](z_ab) x prod_c A_0(c,c) L'_c(z_c)^2  (x nonzero constants),

nonzero for generic nu (L'_c is the first-order motion of block N's line; it must not vanish at a base
point of block 0) and blocks in general position.

**Theorem C (PROVED, given Lemmas 1, 2).** For n >= 2: Q_cyc(n-1) at one product-form point ==> P(n).
*Proof.* Replace the 12 rows E_{N,a}, F_{N,0,a,b} by (pair difference)/delta. At delta = 0 the new family is
the distinct delta = 0 members (independent by Q_cyc) plus the 12 jets, which are independent modulo S_0
by Lemma 1 (the 12 functionals vanish on S_0) and Lemma 2. So the modified family has full rank at
delta = 0, hence for small delta != 0, hence the original family does; u_N = u_0(1 + delta nu) is a
product-form point, so P(n) holds generically (L3). ∎
EXACT-CHECKED (`agent_col_local12.py`): the 18 functionals (6 per line, incl. lower-order checks) vanish on
all 183, 276, 387 members (n = 5, 6, 7) and have rank 12 on the jets, with exactly the zero pattern above.

### 3.5 The flat limit and a pole-order filtration of S_0

* **Filtration (EXACT-CHECKED n = 4, 5, 6; n = 7 dp/tau ranks 93/45 from `agent_col_jets.py`; `agent_col_polar.py`).** For m >= 4:
  dim(S_0 cap {no double poles}) = dim W_m + 6; rank of the longitudinal double-pole data = 9m - 6;
  rank tau(S_0) = 9(m-1); total 9m^2 + 12m - 9 = dim S_0. tau vanishes on Y and on A; dp(W_m) = 0.
  CONJECTURE: the +6 are the simple-pole functions allowed to violate the base condition at the three
  interior base points z_cd (the denominator of the flat limit already vanishes doubly there).
* **Flat limit (EXACT-CHECKED n = 5, 6).** W0(nu) = S_0 (+) jets(nu). Over all nu the jets span only 18 dims
  mod S_0, so W0(nu1) cap W0(nu2) = S_0 (+) 6 dims. **REFUTED:** S_0 = (nu-independent part of the flat
  limit). An intrinsic description of S_0 needs the conditions phi1-phi3 of 3.4.

## 4. Task 3: inductive structures

### 4.0 Append/prepend decomposition (EXACT-CHECKED, but tautological)

S_0 = A + B + span(F_{0,N}), with A = old columns of the append view (blocks 0..m-1 in order, 0' appended),
B = old columns of the prepend view (rotated system (1..m-1,0') with 0 prepended), C = common columns
(t, s in 1..m-1). `agent_col_s0.py (C)`, n = 5, 6, 7: dim A = |A| = 9m^2 - 6m, dim B = |B|, A cap B = C
(dim 9(m-1)(m-2) + 3m), F_{0,N} adds 9. Given independence these equalities are automatic (all are
sub-families), so this is a restatement of Q_cyc, not new structure.

### 4.1 (a) A head-map-free step: KILLED

* Phi_0(w) = w K_0 + L(Lambda_m(w)) with L(lambda) = sum_{t>=1} lambda_tab B_{t,0,a,b} + sum lambda_0ab h_0ab (I - K_0),
  so A = span E + Phi_0(W_m) lies in the explicit space Y := W_m + W_m K_0 (H_0 = span h_0ab(I - K_0) lies in Y).
* EXACT-CHECKED (`agent_col_stepY.py`, n = 4, 5, 6): dim(W_m K_0 cap W_m) = dim W_m - 9m, dim Y = dim W_m + 9m,
  **Y subset S_0**, and the 18m-9 new columns have rank 9(m-1) modulo Y (their tau-data, explicit).
* EXACT-CHECKED (`agent_col_stepmap.py`, n = 5, 6, 7): **Y = A (+) Z** with Z := image of L (9m explicit
  vectors). The 9m-dim space B_tau of new-column combinations with zero tau-data maps onto Y/A = Z by a
  9m x 9m map T0 (rank 9m), and the A-parts Phi_0(w) of these combinations have Lambda_m(w) with all 9m entries
  nonzero and rank 9m. `agent_col_zspan.py`: every Z-vector is a 100% dense combination of the cyclic family.
* Conclusion: Q_cyc(m) <=> [Lambda-free: dim Y = dim W_m + 9m, rank tau(new) = 9(m-1), A cap Z = 0]
  + [Z subset S_0, equivalently T0 invertible], and the last part is Lambda_m-twisted with the same size
  (9m) as the generic append step T of HQ 4.7. Kill criterion met: old parts have dense, non-explicit Lambda.
* Same test for the latest-pair collision (`agent_col_latest.py`, n = 4, 5, 6): its jets are NOT independent
  modulo the explicit space Y_lp = W_{n-1} + W_{n-1} K + span h_K(I-K) + span h_K(I-K Pi) containing S_0;
  the deficit is exactly dim(Y_lp/S_0) = 9n - 15. So AG's Lambda-free S_0 pushes Lambda into the jets.
  In both collisions a ~9m-dimensional Lambda-twisted piece survives ("conservation of head-map content").
* **REFUTED** (`agent_col_lambdaK.py`, m = 3, 4): on W^K = {w : w K_k in W_m} (dim W_m - 9m, for k oldest,
  middle or newest), Lambda_m(w K_k) is not determined by Lambda_m(w) (joint rank 2 x 9m at m = 4).

### 4.2 (b) Iterated collisions: bounded per collision, but no induction

EXACT-CHECKED (`agent_col_iterated.py`, `agent_col_patterns.py`; "clean" = exponents only 0/1 and
#ones = #coinciding pairs):

| pattern | n | exponent-1 count | coinciding pairs | clean |
|---|---|---|---|---|
| nested2 (N->0, N-1->1) | 6, 7, 8 | 24 | 24 | yes |
| crossing2 (N->1, N-1->0) | 6, 7, 8 | 24 | 24 | yes |
| nested3 | 8 | 36 | 36 | yes |
| palindrome (all) | 5, 6, 7, 8 | 42, 108, 54, 156 | same | yes (no at n = 4) |
| period-3 folding | 5, 6 / 7 | 24, 36 / 54 (+ 9 twos) | 24, 36 / 57 | yes / **no** |
| period-2, period-1 | 4..7 | | | no (except n = 4 period 2) |

CONJECTURE CC: a simultaneous collision pattern with independent generic nu's in which no block occurs
more than twice is clean for n >= 5. Each extra non-adjacent collision costs exactly 12, but the delta = 0
problem of the folded configuration still contains an append-type Lambda-twisted step (each fold is an
append of a copy), and three copies of a block create extra delta = 0 relations (period-3, n = 7: rank
336 < 342 distinct members). Killed as an induction mechanism.

### 4.3 (c) Cyclic symmetry: KILLED as stated; an intrinsic-space fact survives

`agent_col_cyclic.py`, same m generic blocks, cyclic configuration cut at block k, C_k = (k, ..., k-1, k'):
* dim(S^(0) cap S^(k)) = dim W_m exactly (m = 4, 5, 6, all k): different cuts share only W_m; there is no
  rotation symmetry relating them (EXACT-CHECKED).
* **S_0 is independent of the order of the middle blocks** (EXACT-CHECKED m = 4, 5, 6: random permutations
  of 1..m-1 and the reversed cycle (0, m-1, ..., 1, 0') give the same span). CONJECTURE I: S_0 = S(0; {1..m-1})
  is an intrinsic space attached to the block set with block 0 doubled, like W_n itself. Consequently
  Q_cyc(m) for one middle order <=> for all orders (given CONJECTURE I).

## 5. Task 4: statements

1. **Theorem C (PROVED):** P(n) <== Q_cyc(n-1), for every n; the jet part is explicit and local
   (product of natural factors at the six base points of block 0). Q_cyc(m) EXACT-CHECKED for m = 4..8
   (so this route reproduces P(n) for n = 5..9, nothing new numerically).
2. **Equivalent forms of Q_cyc(m)** (EXACT-CHECKED m = 4, 5, 6): (i) delta = 0 relations = 12 coincidences;
   (ii) head/body independence (9m^2+18m-6 functions); (iii) Y = W_m + W_m K_0 subset S_0 and dim Y = dim W_m + 9m,
   plus the explicit tau-rank 9(m-1); (iv) T0 (9m x 9m) invertible.
3. **CONJECTURE I** (intrinsic S_0) and **CONJECTURE CC** (clean collisions), evidence above.
4. No statement that both implies P(n) and is plausibly provable for all n by the methods here emerged:
   every form of Q_cyc(m) keeps a 9m-dimensional Lambda_m-twisted part (form (iii): the explicit vectors
   B_{t,0,a,b} (t >= 1) and h_0ab(I - K_0) must lie in the span of the cyclic family; their coefficients are dense).

## 6. Assessment and most promising next step

The oldest-newest collision trades the problem cleanly: the 12 jets are handled by a local, Lambda-free
argument with a product formula (Theorem C), but the delta = 0 problem Q_cyc(n-1) is the generic append
step specialized at u_N = u_0, still Lambda-twisted (9m x 9m). The latest-pair collision does the opposite
(Lambda-free S_0, Lambda-twisted jets). Neither collision removes the head map.

Most promising next step: exploit that S_0 is intrinsic (CONJECTURE I). (1) Prove CONJECTURE I and give S_0
an intrinsic definition (functions with poles <= 2 on L_c, <= 1 elsewhere, base conditions, and the
local conditions phi1-phi3 of 3.4 plus whatever cuts the 6 extra directions of 3.5), with dim = |fam| - 12 by
a residue exact sequence. (2) Then Q_cyc(m) is a spanning statement for an intrinsic space that is
simultaneously spanned by the cyclic families of all m-1! middle orders: the twisted graphs
A_sigma = span E + Phi_0^sigma(W_m) (one for each order of the m-system) all lie in it, so the needed 9m
directions Z could come from differences Phi_0^sigma - Phi_0^sigma' = L(Lambda^sigma - Lambda^sigma'), i.e. from how
the head map changes under reordering the middle blocks, an object that might satisfy a commutator recursion
(AGENT_LIE swap identity) where Lambda itself does not.

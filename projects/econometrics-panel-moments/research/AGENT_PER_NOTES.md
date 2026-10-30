# Persistence limit g = I + eps H, done intrinsically (agent PER, 20-21 Oct 2026)

Angle: the persistence degeneration of the brief, done intrinsically. The setting is
A_t(a,i) = (delta_ai + eps H(a,i)) u_t(i), H(a,a) = 0 (the brief's g = I + eps H^T).
Work with functions and Laurent coefficient vectors, never with cross-point coordinates,
except once as an independent cross-check (sec. 4.2(b)).

**Labels.**
* PROVED: an argument is given here.
* EXACT-CHECKED: exact arithmetic, by one of three methods:
  * (a) "series mod P": eps is a formal variable; power series are truncated at a
    stated order, with coefficients in F_P, P = 1073741789. They are evaluated at random
    points X of F_P^3, at one random product-form parameter point. Each order-m block uses
    both components at >= 3(m+1)^2 + 5 points. This makes the evaluation injective,
    because every eps^m-coefficient that occurs is a zero-sum Laurent vector of pole
    order <= m (sec. 3.1).
  * (b) "over Q": exact rationals.
  * (c) "l-adic": exact rationals, eps = l = 10007, l-adic Smith form (hq_fresh_smith).
* CONJECTURE, REFUTED.

Single-point checks are certificates only for rank lower bounds. A containment or index
value at one point is evidence for the generic statement.

**Scripts.** All are in `exploration/`; run them with `../../../.venv/bin/python <script>`.
Each docstring says what the script does and does not show.

| script | content | runtime |
|---|---|---|
| `agent_per_lib.py` | model, eps-series mod P at points (numpy), DVR saturation; self-test | <1 s |
| `agent_per_expansion.py` | Task 1: closed forms (X1-X5), over Q + l-adic cross-check with `family_eval` | 1 s |
| `agent_per_flatlimit.py` | W^0 = W^naive (N1, n <= 14) and agreement with saturation (N2) | 1-2 min |
| `agent_per_index.py` | (I1) raw B = G intrinsically; (I2) A_k(B') = Pi_k via index; (I3) delta_n; (I4) L_G' = L_B' | 2 min (n <= 8) |
| `agent_per_reduced.py` | A_k(B'), A_k(G'), A_k(F'), Pi_k; `--bigrade`: Lag-1 table | 15 s (n = 3,4); 3 min (n = 5) |
| `agent_per_symbols.py` | DHW symbols sigma_k as Laurent vectors; torus / pole-type gradings; `--initial` | 5-30 s |
| `agent_per_e1.py` | E1: eps L_B' ⊆ L_F' (exact membership); also eps^2 | 15 s (n <= 5); 3 min (n = 6, 7) |
| `agent_per_canonical_check.py` | E1 via canonical R_n: Smith form of D R_n D^-1 (l-adic) | 20 s (n <= 5) |
| `agent_per_psi0.py` | leading map Psi_0: rank formula; `--classes`: naive commutator-class tests | 20 s |
| `agent_per_headmap.py` | (*) normalised head map regular on L_B' | 13 s (n = 4,5); 35 s (n = 6) |
| `agent_per_induction.py` | append step: which DHW columns produce the new canonical vectors | 1 min |

## Summary

1. **Exact model (PROVED).** With c_{t,a,i} = H(a,i) u_t(i)/u_t(a) we have
   l_ta := L_ta/u_t(a) = X_a + eps lam_ta, where lam_ta = sum_{i != a} c_{t,a,i} X_i.
   Put f_ta := X_a/l_ta and nu_ta := sum_{i != a} c_{t,a,i} X_i (e_i - e_a) (linear, zero-sum). Then:
   * K_t(a,a) = f_ta and K_t(a,d) = eps c_{t,a,d} (X_d/X_a) f_ta;
   * E_{t,a} = -eps f_ta nu_ta;
   * B_{t,s,a,b} = -eps (delta_ab + eps c_tab) f_ta f_sb nu_sb;
   * every DHW column, normalised, is F'_{t,s,a,b} = f_ta J'^{(t)}_{s,b}.
   Closed forms to second order are below (sec. 1); they are EXACT-CHECKED.
2. **The flat limit is explicit.** W^0 is the naive limit interpolation space, with
   numerators vanishing at:
   * the FIXED points P_ta = {X_a = 0, lam_ta = 0} (n of them on each coordinate line);
   * length-n "generic fat point" schemes at the three vertices.

   The inclusion W^0 ⊆ W^naive is PROVED. dim W^naive = 9n^2 - 6n is EXACT-CHECKED for
   n <= 14, so W^0 = W^naive for those n.
3. **The canonical lattice realises the pole-order filtration.** Normalise the canonical
   family to B' = {f_sb nu_sb, f_ta f_sb nu_sb}. Its leading-term spaces are exactly
   Pi_k = {v in W^0 : pole order <= k}:
   * A_k ⊆ Pi_k is PROVED;
   * equality is EXACT-CHECKED for n <= 8.

   G spans the SAME lattice as B (raw and normalised). So the brief's "G is
   nondegenerate" holds only relative to B. Intrinsically, B and G are degenerate, with
   index 60, 213, 516 for n = 2, 3, 4 (REFUTED as an intrinsic statement).
4. **Smith-reduced DHW problem: first order suffices for n >= 4.**
   * CONJECTURE E1 (EXACT-CHECKED n = 4, 5, 6, 7 by two independent code paths at
     n = 4, 5): eps L_B' ⊆ L_F'. Equivalently, D R_n D^{-1} with D = diag(eps^[a != b]) has
     Smith exponents in {0, 1} only; R_n itself has exponents in {0, 1, 2}. E1 fails at
     n = 3, where only eps^2 L_B' ⊆ L_F' holds.
   * E1(n) implies det R_n != 0 (PROVED).
   * The relative defect is delta_n = 3(5n^2 - 9n - 2)/2 (EXACT-CHECKED n = 4..8). The
     values at n = 7 and n = 8 were predicted before they were computed.
   * The leading map has an explicit rank 12n + 3 C(n-1,2): the E's, the 9n head sums
     I_t, and 3 C(n,2) commutator classes (EXACT-CHECKED n = 3..6).
5. **Toward a proof (PROVED reductions).**
   * By Krull, E1 <=> eps L_B' ⊆ L_F' + eps^2 L_B'.
   * Appending the latest block: E1(n) together with (*) handles the whole old part
     of E1(n+1). (*) is: the normalised head map Lambda' is regular on L_B'
     (EXACT-CHECKED n = 4, 5, 6).
   * What remains is a first-order statement about the 18n new columns. They are
     coupled: both kinds of new column are needed (EXACT-CHECKED).
6. **Killed.**
   * Torus-weight grading of the reduced problem: REFUTED.
   * Pole-type grading: REFUTED in general.
   * Naive (pair, state) indexing of the commutator classes: REFUTED.
   * "Order <= 2 combinations of raw DHW columns suffice": REFUTED. Intrinsic shifts
     reach 2n + 1.
   * Guess delta_n = 9(n^2 - 3n + 3): REFUTED at n = 6.

## 1. Exact model and second-order closed forms (Task 1)

**1.1 (PROVED).** L_ta = sum_i A_t(a,i) X_i = u_t(a)(X_a + eps lam_ta). Hence

    K_t(a,i) = (delta_ai X_a + eps c_{t,a,i} X_i)/(X_a + eps lam_ta).

This gives the formulas for K_t(a,a) = f_ta and K_t(a,d). It also gives
e_a(I - K_t) = -(eps f_ta/X_a) nu_ta, using sum_{d != a} c_{t,a,d} X_d = lam_ta.

Consequences:
* E = -eps f nu and X_a K_t(a,b)/X_b = f_ta (delta_ab + eps c_tab), which gives the
  formula for B.
* This is the brief's K_t = (I + eps Lam_t)^{-1}(I + eps Q_t), with
  f_ta = 1/(1 + eps mu_ta), mu_ta = lam_ta/X_a = Lam_t(a), and Q_t = D_{u_t X}^{-1} H D_{u_t X}.
* In path form, X_b e_b K_{w1}...K_{wm} = sum over paths b = c_0 -> ... -> c_m of
  X_{c_m} prod_j f_{w_j, c_{j-1}} (delta + eps c_{w_j, c_{j-1}, c_j}). The X-ratios
  telescope.
* Every coefficient of eps^k is a Laurent polynomial in X with poles only on the
  coordinate lines. Its coefficients are polynomials in H and the torus ratios.

**1.2 Closed forms (PROVED by expansion; EXACT-CHECKED over Q, n = 2, 3, 4, two points each,
against series computed from the DEFINITION of A_t by series division).** Take a word
W = K_{w_1}...K_{w_m} with distinct letters and t not in w, and put
N_u = Q_u - Lam_u (zero row sums). We use the identity

    nu_ua N_v = sum_{c != a} c_{u,a,c} nu_vc - mu_ua nu_va        (exact).

For a = b:

    [eps^1] h_taa(I-W) = -sum_{u in w} nu_ua
    [eps^2] h_taa(I-W) =  mu_ta sum_u nu_ua + sum_u mu_ua nu_ua - sum_{i<j} nu_{w_i a} N_{w_j}

For a != b:

    [eps^1] h_tab(I-W) = 0
    [eps^2] h_tab(I-W) = -c_tab sum_u nu_ub
    [eps^3] h_tab(I-W) =  c_tab [mu_ta sum_u nu_ub + sum_u mu_ub nu_ub - sum_{i<j} nu_{w_i b} N_{w_j}]

For E: E^{(k)}_{s,a} = -(-mu_sa)^{k-1} nu_sa.

The first order sees only the letter set. For DHW differences, with s_min the smallest
block != t:

    [eps^2](F_{t,s,a,a} - F_{t,s_min,a,a}) = -sum_{v<s, v != t} X_a e_a [N_s, N_v]
    X_a e_a [N_s, N_v] = sum_{c != a}(c_{s,a,c} nu_vc - c_{v,a,c} nu_sc) + mu_va nu_sa - mu_sa nu_va.

Exactly, F_{t,o_i} - F_{t,o_1} = h_tab [K_{o_1}...K_{o_{i-1}}, K_{o_i}] K_{>o_i}, a
commutator.

The l-adic cross-check (X5) compares with the project's `family_eval` at eps = l: the
valuation of (exact - series to order 4) is 5 > 4 (n = 3, 4). A sensitivity check
confirms the tests are not vacuous: perturbing the nu-N identity or f makes them fail.

## 2. The flat limit W^0 (Task 2, first half)

Notation:
* L_X := C[[eps]]-span of a family X.
* L_sat := saturation: elements of W(eps) whose eps-expansion has no negative powers.
* W^0 := {leading coefficients} = L_sat/eps L_sat (dim d = 9n^2 - 6n).
* A_k(L) := {[eps^k] w : w in L, w = O(eps^k)}, so A_0 ⊆ A_1 ⊆ ... ⊆ W^0.
* dim A_k(L) = #{Smith exponents of L in L_sat that are <= k}.

**2.1 (PROVED).** Every base point of W_n degenerates to a fixed or vertex scheme:
* l_ta ∩ {X_a = 0} = P_ta := {X_a = 0, lam_ta = 0} is independent of eps.
* l_ta ∩ l_tb = eps q_t + O(eps^2) in local coordinates (X_a, X_b) at X_c = 1, with
  q_t = (-c_{t,a,c}, -c_{t,b,c}).

Assume the evaluation matrix [m(q_t)] (monomials m of degree < k) has full rank; this is
a generic condition, and the script verifies it. Then the flat limit of
span{ev_{p_t(eps)}} is spanned by G -> sum_t alpha_t G_j(q_t), with alpha orthogonal to
all monomials of degree < j at the q's. Proof: extend alpha in ker[m(p_t(eps))/eps^{deg m}],
which is a smooth family because its limit has full rank, and rescale by eps^{-j}.
Denote by zeta_c this length-n vertex scheme.

Pairing with the numerators g(eps) = eps^k g_0 + ... then gives W^0 ⊆ W^naive, where

    W^naive := {(X_i g_i/(X0X1X2)^n)_i : sum_i X_i g_i = 0, g_i in I({P_ta} ∪ zeta_0 ∪ zeta_1 ∪ zeta_2)_{3n}}.

**2.2 (EXACT-CHECKED: one linear system mod P per n, no eps-series needed).**
dim W^naive = 9n^2 - 6n for n = 1..14 at a random point with parameters up to 1e8.
Hence W^0 = W^naive for these n, generically. With parameters up to 60, two blocks can
share a ratio u_t(c)/u_t(b), so points P_ta coincide; this gave spurious excesses of
2 or 4 at n = 9..12.

**2.3 (EXACT-CHECKED, series mod P, n = 2, 3, 4).** The saturations of the raw B and DHW
families have leading rows spanning exactly W^naive (evaluated at the same points).

**2.4 B = G intrinsically; G is not intrinsically nondegenerate.**
* REFUTED in the intrinsic reading: the brief says "G is exactly nondegenerate". But
  G_{t,r,a,a} and E_{r,a} have the same leading term -eps nu_ra for every t.
* EXACT-CHECKED (I1), raw families: [L_sat : L] is 60, 213, 516 for both B and G
  (n = 2, 3, 4). For DHW it is 60, 243, 579, i.e. +30 and +63, which reproduces the
  canonical defects.
* EXACT-CHECKED (I4), normalised: L_G' = L_B' by two exact containments (n = 3, 4, 5).
* Theorem A's nondegeneracy is therefore relative to B, and the flat limit cannot be
  read off from G directly. It is given by 2.2 instead.

## 3. The canonical lattice realises the pole-order filtration

Normalise every member to valuation 0:
* B' = {eta_sb = f_sb nu_sb, beta_tasb = f_ta f_sb nu_sb}; these are E/(-eps), B/(-eps)
  and B/(-eps^2 c_tab);
* F' = {E/(-eps), F/(-eps) (a = b), F/(-eps^2 c_tab) (a != b)} = {eta, f_ta J'^{(t)}_{s,b}}.

The pole order of a Laurent monomial X^m is sum_j max(0, -m_j). Put
Pi_k := {v in W^0 : pole order <= k}.

**3.1 (PROVED).** Every eps^i-coefficient of eta, beta, F' (and G') has pole order <= i.
* For eta and beta it is a sum of mu^p mu^{i-p} nu.
* For F', [eps^{i+1}](X_b e_b W) is a sum of path terms.
  * Each eps-unit is either an off-diagonal step, which carries no pole after
    telescoping, or a factor -mu at the current state.
  * If all i+1 units are mu's, the path never moves, and the prefactor X_b cancels one
    pole.

Hence A_k(L) ⊆ Pi_k for L = L_B', L_G', L_F'.

**3.2 (EXACT-CHECKED (I2), series mod P, n = 3..8).** [L_sat : L_B'] = sum_k (d - dim Pi_k)
(114, 324, 696, 1278, 2124, 3276). With 3.1 this forces A_k(L_B') = Pi_k for every k.
It was also checked directly for n = 2..5 (`agent_per_reduced`); the same holds for G'.

dim Pi_k:

| n | dim Pi_k, k = 0, 1, 2, ... |
|---|---|
| 3 | 6, 24, 45, 63 |
| 4 | 6, 24, 54, 84, 108, 120 |
| 5 | 6, 24, 54, 96, 135, 165, 189, 195 |
| 8 | 6, 24, 54, 96, 150, 216, 294, 360, 408, 450, 486, 516, 528 |

* For k <= n-2, Pi_k is the full space of zero-sum degree-1 Laurent vectors of pole order
  <= k, of dimension 6(k+1)^2.
* The conditions start at pole order n-1 (P_ta) and at high pole order (vertices).

## 4. The Smith-reduced DHW problem (Task 2, second half; kill criterion)

**4.1 DHW lags the pole-order filtration by at most one step.** EXACT-CHECKED, series mod P,
`agent_per_reduced --bigrade`: Pi_{k-1} ⊆ A_k(L_F') ⊆ Pi_k for all k.
* For n = 4, 5 this was checked directly.
* For n = 6, 7 it follows from E1 (PROVED implication, 4.3).
* For n = 3 it fails at k = 4: dim A_4 = 57 < 63 = dim Pi_3. The 6-dim lag-2 piece is
  reached at k = 5.

dim A_k(L_F') against dim Pi_k:

| n | k = 0..8 |
|---|---|
| 3 | 6, 24, 39, 45, 57, 63 |
| 4 | 6, 24, 48, 63, 84, 108, 120 |
| 5 | 6, 24, 51, 69, 108, 135, 165, 189, 195 |

The codimensions sum to 30, 63, 117 (= v(det R_n)).

**4.2 Conjecture E1, and the defect formula.**
* **CONJECTURE E1.** For n >= 4, eps L_B' ⊆ L_F'. In words: eps times every normalised
  canonical vector is a C[[eps]]-combination of normalised DHW columns.
* Canonical form. With R_n the canonical matrix (F_j = sum_i B_i R_ij mod E) and
  D = diag(eps^[a != b]) over labels (t,s,a,b), the normalised matrix is the conjugate
  R' = D R_n D^{-1}. E1 <=> the Smith exponents of R' lie in {0, 1}. Equivalently,
  (R_n^{-1})_{ji} has a pole of order <= 1 + [a_j != b_j] - [c_i != d_i]. Here j is an
  F-label (t,s,a,b) and i a B-label (u,v,c,d).

EXACT-CHECKED:
* (a) Series mod P (`agent_per_e1`): exact membership of all eps B'_j in L_F', with e =
  max saturation shift so that eps^e L_sat ⊆ L_F' and the test is exact.
  * True for n = 4, 5, 6, 7 (seed 21), and for n = 4, 5 at seed 77.
  * At n = 3 it is false (ranks 171 vs 177), while eps^2 L_B' ⊆ L_F' is true.
* (b) l-adic, independent code path (`agent_per_canonical_check`, the project's
  R_matrix). Smith exponents:

| n | R_n | R' = D R_n D^{-1} |
|---|---|---|
| 3 | 0^36 1^6 2^12 | 0^30 1^18 2^6 |
| 4 | 0^60 1^33 2^15 | 0^45 1^63 |
| 5 | 0^90 1^63 2^27 | 0^63 1^117 |

The defect, EXACT-CHECKED (I3), series mod P:

    delta_n := [L_B' : L_F'] = v(det R_n) = 30, 63, 117, 186, 270, 369   (n = 3..8)
    delta_n = 3(5n^2 - 9n - 2)/2   for n = 4..8 (and n = 2: 0)          [CONJECTURE for all n >= 4]

* 270 (n = 7) and 369 (n = 8) were predicted from n = 4, 5, 6 before they were computed.
* REFUTED: the earlier guess 9(n^2 - 3n + 3), which gives 189 != 186 at n = 6.

**4.3 Consequences (PROVED).**
* E1(n) implies det R_n != 0. Indeed eps L_B' has rank d, so the d DHW/E functions are
  independent over C((eps)).
* E1 => Lag-1, because A_k(eps L) = A_{k-1}(L).
* Lag-1 alone already gives full rank: A_{K+1}(F') ⊇ Pi_K = W^0.
* (Krull) E1 <=> eps L_B' ⊆ L_F' + eps^2 L_B'. Proof: iterating gives
  eps L_B' ⊆ L_F' + eps^k L_B' for all k. Then use the intersection of
  eps^k (L_B'/L_F') over k, which is 0 by Krull's intersection theorem.
  * So only the coefficients modulo eps^2 matter.
* Under E1, rank Psi_0 = d - delta_n, where Psi_0 : span_C(F') -> L_B'/eps L_B'.

**4.4 The leading map Psi_0 (EXACT-CHECKED, series mod P, n = 3, 4, 5, 6).**
Split DHW = {eta} ∪ {I'_t = F'_{t,s_min}} ∪ {D'_{t,s} = F'_{t,s} - F'_{t,s_min}}.
* rank_{mod eps L_B'} {eta} = 3n.
* {eta, I'} = 12n (independent).
* {all D'} = 3 C(n,2) = 9, 18, 30, 45.
* All of DHW: f(n) = 12n + 3 C(n-1,2) = 39, 57, 78, 102. The same value is reached using
  only the D' with a = b, or only those with a != b.
* Under E1 this gives delta_n = d - f(n) = 3(5n^2 - 9n - 2)/2 exactly. The two formulas
  in 4.2 are one fact.
* For n = 3, f(3) = 39 also holds, but E1 fails. The canonical form shows 18 exponents 1
  and 6 exponents 2 (rank R'(0) = 39 - 9 = 30).

So the order-0 part of the reduced problem is combinatorial. It consists of the E's and
head sums plus a 3 C(n,2)-dimensional space of commutator classes, of which 3 C(n-1,2)
are new modulo E and I.

REFUTED, naive descriptions of the commutator classes (`--classes`, n = 4, 5):
* class(D'_{t,s,a,b}) is NOT independent of the head state a: the differences have rank
  15 (n = 4) and 27 (n = 5).
* Nor is it independent of t for t > s: rank 3 and 9.
* The single-commutator columns h_tab [K_u, K_v] K_{>v} span 6 (not 3) classes per head.
  Heads sharing the pair {0,1} span 9 (n = 4) and 12 (n = 5).

**4.5 The DHW symbols sigma_k := (A_k(F') + Pi_{k-1})/Pi_{k-1} ⊆ gr_k = Pi_k/Pi_{k-1}.**
EXACT-CHECKED, series mod P + the W^naive basis, `agent_per_symbols`.

dim sigma_k:

| n | dim sigma_k, k = 0, 1, 2, ... |
|---|---|
| 3 | 6, 18, 15, 0 |
| 4 | 6, 18, 24, 9, 0, 0 |
| 5 | 6, 18, 27, 15, 12, 0, 0, 0 |
| 6 | 6, 18, 30, 21, 12, 15, 0, ... |

The sum is f(n).

* **sigma_k = 0 for k >= n** (n = 3..6). At the pole orders where the P_ta and vertex
  conditions act, DHW has no own symbols. Everything there is delayed by exactly one
  level.
* Under E1 the order-1 map Psi_1 : ker Psi_0 -> coker Psi_0 is an isomorphism. It is
  block-triangular for the pole-order filtration, with diagonal blocks
  (delayed elements at level j+1) -> gr_j/sigma_j of sizes:
  * n = 4: 6, 21, 24, 12;
  * n = 5: 3, 27, 27, 30, 24, 6.
* At k = 2 (n = 4) the six delayed directions are exactly two in each sector X_a^{-2}.
  This is the same under two lex orders. There is one per sector at n = 5 and none at
  n = 6.

**Kill criterion (Task 2): NOT met.** The reduced problem has visible structure:
* first order suffices (E1, n >= 4);
* an explicit order-0 rank;
* lag <= 1 in the pole-order filtration, with block sizes O(n).

What is NOT understood is the diagonal blocks of Psi_1 (sizes up to ~6n). Most of them
sit at pole orders >= n, where sigma = 0.

## 5. Gradings, term orders, Lie description (Task 3)

* **Torus-weight grading: REFUTED.**
  * gr_k Pi is monomial for k <= n-2, but the symbols are not. At n = 4, sigma_2 is
    24-dimensional, while its projections onto single monomials have total dimension 30.
  * At n = 5, sigma_3 gives 15 vs 21.
  * So no torus-weight block-diagonalisation exists.
* **Pole-type grading** (which variables carry the poles): sigma_2 is pole-type graded
  for n = 4, 5, but not for n = 3 (15 vs 21), and sigma_3 is not graded at n = 5
  (15 vs 21). REFUTED as a general block-diagonalisation.
* **Pole-order filtration: SURVIVES** as a block-triangular structure (4.1, 4.5).
* **Term order.** The missing initial monomials at k = 2 form a clean pattern (4.5). For
  k >= 3 they spread over all pole types, with no simple description found. A
  distinct-leading-monomial proof would need explicit delayed (order-1) elements, which I
  did not find. Not pursued further.
* **Lie description.** The order-0 DHW-specific directions are commutator classes
  (3 C(n,2)-dimensional, 4.4). They are not indexed by (pair, state) in the naive way.

## 6. Toward an inductive proof of E1 (Task 4)

Append the latest block N; in normalised form

    Phi_n(w) = w K_N + sum_tab Lambda'_n(w)_tab B'_{t,N,a,b}.

Here Lambda' = n_ab Lambda, with n_aa = -eps and n_ab = -eps^2 c_tab, and Lambda is the
project's head map (`agent_ag_lib.head_map_matrix`). This is PROVED, being the normalised
form of AG 1.1. Also Phi_n(F'^{(n)}_{t,s}) = F'^{(n+1)}_{t,s} and
Phi_n(eta_sa) = eta_sa - eta_Na.

* **(*) CONJECTURE, EXACT-CHECKED** (series mod P; n = 4, 5 at two seeds, n = 6 at one;
  `agent_per_headmap`). Lambda'_n(L_B') ⊆ C[[eps]]^{9n}: the head sums of the
  F'-coordinates of eps*beta vanish mod eps. The test is not vacuous: the constant-term
  matrix has rank delta_4 = 63, and a wrong head map gives rank 9.
* **Old part (PROVED, given E1(n) and (*)(n)).** For x in L_B'^{(n)}, we have
  Phi_n(eps x) in L_F'^{(n+1)}. Hence
  eps x K_N ∈ L_F'^{(n+1)} + eps span_{C[[eps]]}{B'_{t,N,a,b}}.
  In particular this covers eps G'^{(n+1)}_{t,r} = eps G'^{(n)}_{t,r} K_N for old t, r.
  Use L_B'^{(n+1)} = L_G'^{(n+1)} = span{eta, G'_old, B'_{t,N}, G'_{N,r}}; this lattice
  equality is EXACT-CHECKED (I4). With it, and with Krull (4.3), we get the reduction
  (PROVED given E1(n), (*)(n)):

      E1(n+1)  <=  eps B'_{t,N}, eps G'_{N,r}  ∈  L_F'^{(n+1)} + eps^2 L_B'^{(n+1)}.

  Separately, EXACT-CHECKED at m = 5:
  eps B'^{(n+1)}_{t,s} (old t, s) ∈ L1 + eps span{B'_{t,N}} + eps^2 L_B'. Given this,
  G'_{N,r} may be replaced by B'_{N,s} in the reduction, which is the form tested below.
* **New part (EXACT-CHECKED, `agent_per_induction`, m = n+1 = 4, 5).** It remains to show
  eps B'_{t,N} and eps B'_{N,s} ∈ L_F'^{(n+1)} + eps^2 L_B'^{(n+1)}. Neither family lies in L1 + eps^2 L_B', where L1 = appended old columns + E.
  Nor does
  * eps B'_{t,N} lie in L1 + {F'_{t,N}} (the commutators h[Pi_(t), K_N]) + eps^2 L_B',
  * nor eps B'_{N,s} in L1 + {F'_{N,s}} + eps^2 L_B'.
  Both families lie in the full lattice. So the step is a coupled 18n-dimensional
  first-order statement. The old system enters only through Lambda'_n mod eps on L_B'^{(n)}.
  * Consistency: at m = 4 (from n = 3, where E1 fails) the old part fails, as it must.
* **Bug record.** The first version of `agent_per_induction` selected canonical targets by
  label 'F' instead of 'B'. The target sets were empty and all tests vacuously true; this
  was caught by a Krull contradiction. It is fixed (labels 'B' plus a size assertion), and
  only the fixed results are reported.
* **Proof sketch of the goal from E1** (status: the gap is the induction step):
  1. Base: E1(4) holds, EXACT-CHECKED; n <= 3 is handled by the project's certificates.
  2. Assume E1(n) and (*)(n), for n >= 4.
  3. The old part of E1(n+1) follows (PROVED above).
  4. Show the coupled new-column statement mod eps^2 (OPEN), and propagate (*) to n+1
     (OPEN; the old heads propagate by AG 1.2 when the E-coefficient sums are regular).
  5. Krull gives E1(n+1), and 4.3 gives det R_{n+1} != 0.

## 7. Bugs fixed during this run and final re-runs

* `agent_per_e1.containment` first used only component 1 at the first points for the
  order-m blocks. That is not injective on zero-sum vectors; it is fixed (both components).
  Results were unchanged.
* `agent_per_reduced.A_spaces` has the same coordinate fix and a precision guard
  kmax <= K - 2, since off-diagonal rows lose two orders. An earlier n = 5, k = 8 row was
  invalid for this reason.
* `agent_per_induction` had the label bug above.
* The small-parameter artefact in N1 is fixed.

Everything in this note was re-run after the fixes (21 Oct).

## 8. Most promising next step

**Prove the induction step of E1 at first order.** Base: n = 4. The old part is done,
given (*). What remains:
1. **Coupled new-column step.** Show that the 18n new DHW columns span
   eps·{B'_{t,N}, B'_{N,s}} modulo L1 + eps^2 L_B'^{(n+1)}. Here L1 is the appended old
   columns plus E. It is an 18n-dimensional, first-order (eps^2-truncated) linear
   statement whose inputs are:
   * the commutators h_tab[Pi_(t), K_N];
   * the new-head inputs f_Na J'^{(S)}_{s,b};
   * the leading head map Lambda'_n(.)(0) on L_B'^{(n)}.
   Compute this 18n x 18n matrix intrinsically, and test whether it is triangular in the
   pole-order filtration with explicitly invertible diagonal blocks.
2. **Propagate (*).**

A parallel, coordinate-free target is Lag-1 block by block in W^naive. For pole orders
j >= n (sigma_j = 0) one must show that the delayed DHW elements realise the whole top
graded piece gr_j Pi. That piece is where the fixed points P_ta and the vertex schemes act,
so it is a concrete interpolation-type statement.

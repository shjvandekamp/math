# A fresh approach to det H_q (full equation-(24) independence, Q = 3)

## PROOF DASHBOARD (read this first after any restart)

**Target.** For Q = 3, every T >= 1 and every initial outcome, the
equation-(24) family is a basis of the fixed-effect-free moment space M_T
for (gamma, beta, x) in an open dense subset of the economic domain
pi_t(q,r) = exp(gamma_qr + x_t beta_q). Then: general Q (T = 4 first).

**Lemma tree** (status as of 19 Oct 2026, evening):

| id | statement | status |
|---|---|---|
| L0 | dim M_T = &#124;family&#124; on the economic generic region | PROVED (project, Lean) |
| L1 | exact split: T-family = 3 lifts of (T-1)-family + E/F quotient images in W_n, n = T-2 | PROVED (project) |
| L2 | (E,B) basis of W_n; new columns independent iff det R_n != 0 | PROVED (project) |
| L3 | economic domain Zariski dense in product-form family; one nonzero point per n suffices | PROVED (sec. 2.1), to write in HQ_PROOF |
| L4 | append the latest block: old x old block of R_{n+1} is Gamma R_n; new-head rows vanish on old columns | PROVED + EXACT-CHECKED (sec. 2.0) |
| A  | *standard-tail family* G_{t,r,a,b} = B_{t,r,a,b} K_{>r} with E is a basis of W_n for all n, det R^G_{n+1} = det Gamma det R^G_n prod kappa | PROVED (sec. 4) + EXACT-CHECKED (hq_fresh_standard_tail.py) |
| L5 | det R_n != 0 for the equation-(24) family F, all n; equivalently det C_n != 0, C_n = transition F -> G | CONJECTURE (the gap) |

**Next-steps queue** (top = next):
1. Admissibility of (J_t) (sec. 4.3): induct with the multiplication structure.
2. Persistence (near-identity) limit: Lie-algebra form of C_n's defect.
3. Write HQ_PROOF.md skeleton with L0-L4 and Theorem A fully proved.

**Tools.** math/.venv has python-flint 0.9, sympy 1.14, numpy (gitignored).

Working note, started 18 October 2026. Everything here is labelled
PROVED, EXACT-CHECKED or CONJECTURE. Nothing in this note is Lean
checked. The goal is the one open problem of the project: generic
linear independence of the particular equation-(24) family of
Dano–Honoré–Weidner for every T >= 5, which the project reduced to
det H_q != 0 (LC113)/(IT17).

## 0. The problem restated from first principles

Periods 1..T, states {0,1,2}, fixed initial state y_0. Transition
weights pi_t(q,r) > 0. The true path probability is
p_y = prod_t pi_t(y_t,y_{t-1}) eta_{y_t} / L_{t,y_{t-1}}(eta).
A generation order tau (a permutation of {1..T} with tau_T = T,
tau_0 := 0) defines the transformed chain
p^tau_y = prod_k pi_{tau_{k-1}+1}(y_{tau_k}, y_{tau_{k-1}}) eta_{y_{tau_k}} / L_{tau_{k-1}+1, y_{tau_{k-1}}}.
Both have the same denominators, so S^tau = p^tau/p is a ratio of
monomials in pi. The source family (24) consists of
m = g(y) [1{y_{s1}=q0} S^{tau1} - 1{y_{s2}=q0} S^{tau2}].
The moment space is M_T = {m : sum_y m_y p_y(eta) = 0 for all eta}.
PROVED (project): dim M_T = 3^T - C(3T,2) + 6(T-1) = |family| on an
explicit open dense economic region. Hence independence <=> spanning.

### 0.1 Exact split (PROVED, SOURCE24_INDUCTION.md, re-derived here)

Rows whose shared set contains period 1 are three disjoint indicator
lifts of the complete (T-1)-period family (initial state y_1). By
induction they span the lifted space (dimension 3 dim M_{T-1}). The
remaining rows (j = 0, or j = 1 with shared time >= 2) number
3n(3n-2), n := T-2. Their images under the quotient map
m -> C_i(X) = sum_{y_1 = i} m(y) p_y(X), after removing nonzero
constant column factors, are the rational row vectors

    E-type (after the exact constant-coefficient j=0 reduction):
        E_{s,a}     = X_a e_a (I - K_s),                   s in [n], a in {0,1,2}
    F-type (j = 1):
        F_{t,s,a,b} = X_a K_t(a,b) e_b (I - K_s prod_{u in [n] \ {s,t}, increasing} K_u),  t != s.

Here K_t = diag(L_{t0},L_{t1},L_{t2})^{-1} A_t diag(X) is the
row-stochastic transfer matrix of block t (block t = the transition
following outcome y_{t+1} in paper time), L_{ta} = sum_i A_t(a,i) X_i.
All of (24) for T periods is independent iff the (T-1)-family is and
these 3n(3n-2) vectors are linearly independent over R.
Every insertion and polynomial head is kept: the vectors are the
actual source images, nothing is dropped.

### 0.2 The quotient space (PROVED, project lemma; re-derived)

W_n = {(X_i g_i / D)_i : g_i in I(Z)_{3n}, sum_i X_i g_i = 0},
D = prod of the 3n lines, Z = the 6n base points. dim W_n = 3n(3n-2).
Writing g = X x u (cross product) identifies

    W_n  ~=  H^0(P^2, Q(3n-1) ⊗ I_Z),

sections u in S_{3n-1}^3 modulo X·S_{3n-2} (Euler sequence) that are
radial, u(p) || p, at the 6n base points: twisted tangent fields
vanishing at Z. The double-pole residue of v at a cross point
P = L_{ta} ∩ L_{sb} is, up to the invertible factor diag(X(P))/D'(P),
the tangent vector P x u(P). The project's canonical basis
{E_{s,a}} ∪ {B_{t,s,a,b} = X_a K_t(a,b) e_b (I - K_s)} corresponds to
the "monomial" fields
    u_E = (D/L_{sa}) (e_a x alpha_{sa}),
    u_B = A_t(a,b) X_a (D/(L_{ta} L_{sb})) (e_b x alpha_{sb}),
constant direction times a product of linear forms.

### 0.3 Torus structure of the economic family (PROVED, elementary)

With pi_t(q,r) = exp(gamma_{qr} + x_t beta_q) = g(q,r) u_t(q),
A_t(a,i) = g(i,a) u_t(i), so L_{ta}(X) = l_a(u_t ∘ X) and
K_t(X) = K(u_t ∘ X) for ONE fixed rational matrix function K and one
fixed line triple l_a = sum_i g(i,a) X_i. All blocks are translates of
one block by torus elements u_t = exp(x_t beta), which lie on a common
one-parameter subgroup of the torus.

## 1. Special-point evidence (EXACT-CHECKED)

`exploration/hq_fresh_special_points.py` computes the rank of the raw
family K = M diag(A_y) modulo 1000003 at rational points. A full
modular rank proves full real rank at that point, hence generic
independence over the set of tables for which the point is a limit of
the family (a nonzero minor stays nonzero on a dense open set).

| T | family | no state dep. u_t(q) | time-homog. g(q,r) | product u_t(q)g(q,r) | g(q,r) w_q^(t+1) | random | powers of 1/64 |
|---|---:|---:|---:|---:|---:|---:|---:|
| 4 | 33 | 33 | 27 | 33 | 33 | 33 | 33 |
| 5 | 162 | 138 | 117 | 162 | 162 | 162 | 162 |
| 6 | 606 | 489 | 429 | 606 | 606 | 606 | 606 |

Conclusions. (i) State dependence is essential: without it the family
is dependent already at T = 5, so no argument can factor through the
static model. (ii) Time variation is essential. (iii) The product
(economic) form keeps full rank at T = 4,5,6, including with u_t(q) =
w_q^(t+1) (a point of the economic family itself). These are finite
checks for T <= 6 only; they prove nothing for T >= 7.

### 1.1 Degenerate product-form points (EXACT-CHECKED, single points)

`exploration/hq_fresh_degenerations.py` (re-run 19 Oct). Table
pi_t(q,r) = g(q,r) u_t(q); a full modular rank at one rational point
proves generic independence for every family containing that point; a
drop proves nothing. Rank / family size:

| case | T=4 | T=5 | T=6 |
|---|---:|---:|---:|
| generic G, generic u | 33 | 162 | 606 |
| G = J + I (S_3-symmetric), generic u | 33 | 162 | 606 |
| project witness G, u = (1,2,5)^(t+1) (economic point) | 33 | 162 | 606 |
| Vandermonde (conic) G, generic u | 33 | 162 | 606 |
| u_1 = u_0 (two earliest periods equal) | 33 | 162 | 606 |
| u_{T-1} = u_{T-2} (two latest blocks equal) | 33 | 144 | 516 |
| G with one zero entry | 18 | 81 | 279 |
| G lower / upper triangular, G = I | 12/0/0 | 38/0/0 | 91/0/0 |

The two earliest periods never enter the top quotient W_n (they are
peeled by the lift), so u_1 = u_0 is harmless; equal *quotient* blocks
make the line configuration non-reduced and lose rank. Zeros in G
destroy rank massively: monomial-limit (tropical) arguments must keep
all nine g(q,r) at comparable leading order or account for this.

### 1.2 det R_3 (EXACT-CHECKED, two points)

`exploration/hq_fresh_residue_det.py`: R_2 = I exactly; the E/B
expansion of every F column is reconstructed exactly; det R_3 is a
ratio whose denominator is a product of natural geometric quantities
(cross-point coordinates, third-line values) and whose numerator has a
86-100 digit cofactor free of natural primes. So there is no product
formula at generic points. This does *not* exclude a monomial leading
term under a degeneration (every nonzero polynomial has one under a
generic weight); it only excludes exact triangularity.

## 2. Route chosen

### 2.0 Append-the-newest-block structure (L4; PROVED, EXACT-CHECKED)

Order blocks by time, 0..n-1 old, n new (latest). The suffix of every
old column F_{t,s,a,b} is increasing, so the new kernel enters as the
*last* factor: F'_{t,s,a,b} = h (I - W K_n), h = X_a K_t(a,b) e_b,
W = old word.

*(A1)* At an old cross point P, K_n is regular and h has a single pole,
so rho_P(F') = -[L L' h W]_P K_n(P) = rho_P(F) K_n(P). Right
multiplication by the stochastic K_n(P) preserves the zero-sum plane
and has determinant det K_n(P) = det A_n prod_i P_i / prod_a L_{na}(P)
there. Hence the old x old block of R_{n+1} is Gamma R_n with Gamma
block diagonal and invertible on the geometric open set.

*(A2)* At a new cross point P = L_{uc} cap L_{nd} the only new pole of
F' is row d of K_n, whose residue is e_d (x) v_{nd}. So rho_P(F') is a
multiple of v_{nd}(P): the new-head rows (coefficients of B_{n,u,d,c})
vanish on every old column. With rows (old, N_h, N_s) and columns
(old, F_{n,s,.,.}, F_{t,n,.,.}):

    R_{n+1} = [ Gamma R_n  Y1   Y2  ]
              [ 0          Z11  Z12 ]
              [ X2         Z21  Z22 ]

`exploration/hq_fresh_append.py` checks (A1) and (A2) exactly
(1620 and 1782 identities at n = 2, 3). Consequently
det R_{n+1} = det Gamma det R_n det S_n with the 18n x 18n Schur
complement S_n; the induction needs only det S_n != 0. This is the
precise form of L5.

### 2.1 Expert plan (written 19 Oct 2026, before the new computations)

**Is H_q the right object?** H_q came from a *prepend* elimination, which
creates the correction Z_T. Appending the latest block instead gives the
exact block Gamma R_n (sec. 2.0), so the right object is the Schur factor
f_n := det R_{n+1} / (det Gamma det R_n) = det S_n, a rational function
of the newest block's torus position u_n with the old blocks as
parameters. Proving f_n not identically zero for each n, at one point
of the product-form family, is the whole induction step (L5).

**Economic genericity is free (L3).** pi_t(q,r) = g(q,r) u_t(q) with
u_t = exp(x_t beta). For beta with Q-linearly independent coordinates,
x -> (exp(x_t beta))_t is Zariski dense in the torus^T (distinct
exponentials are linearly independent), so a polynomial vanishing on
the economic domain vanishes on the whole product-form family. Hence
one nonzero point of det R_n on the product-form family (complex or
real, possibly a limit point handled by valuations) gives an open dense
economic region. Every degeneration below stays in that family.

**What an interpolation geometer sees.** W_{n+1} = H^0(T(3n+1) ⊗ I_Z),
and the newest block's cubic C gives the residual sequence
0 -> W_n --(·C)--> W_{n+1} -> (residues on the three new lines) -> 0
(the left map is the inclusion of vectors without new poles). This is
Horace with respect to the cubic of the new block. Its defect is that
appended old columns are not in W_n; their traces are *longitudinal*
(proportional to v_{nd} on L_{nd}). Specialising the new block toward a
coordinate line (torus boundary) is the differential-Horace move: the
limit splits into the old plane and a thin strip around the line, where
old kernels become *binary* (state i never entered) and concurrent. The
project already owns binary theorems; the strip is where they belong.

**Routes, in order, each with a kill criterion fixed in advance.**

1. *Newest-block torus degeneration* (primary). Old blocks generic and
   fixed; u_n = lambda(eps) u_0 along weight w (coordinate, two-equal,
   generic). Compute the eps-valuation and leading coefficient of f_n
   (Laurent elimination over F_p((eps))), and the Smith exponents of
   R_{n+1}(eps). Success: some w where the leading coefficient is a
   product of natural nonzero quantities, or equals a determinant of a
   binary/old-type matrix already known to be nonzero, uniformly in n.
   Kill: for n = 2, 3, 4 and all 13 coordinate-type weights the
   leading coefficient carries a growing irreducible factor (no natural
   factorisation).
2. *Full staircase degeneration* along the economic subgroup:
   u_t = lambda(eps)^{k_t}, k_t rapidly increasing (nested limits).
   Success/kill as in route 1, for det R_n itself.
3. *Intrinsic head map.* The Schur factor depends on the old family
   only through the 9n head sums lambda_{tab} = sum_s (R_n^{-1} x)_{tsab}.
   Compute Lambda_n = (head sums) o R_n^{-1} and test whether it equals
   a short combination of natural functionals (residues/values at base
   points, vertices). Success: closed formula, then the induction is
   explicit. Kill: Lambda_n dense and unstructured at n = 3, 4.
4. *Raw-family initial forms* (algebraic statistics). Source moments are
   cylinder functions (each depends on <= j + 8 coordinates); test
   whether economic tropical weights give independent initial forms in
   the tensor basis {1, e_1, e_2}^{⊗T}. Kill: no weight among 500 random
   and all structured economic weights gives independence at T = 5.

**Software.** python-flint (nmod_mat, nmod_poly) for exact modular and
Laurent-series linear algebra; Fraction/fmpq for exact identities;
Singular / Macaulay2 for Hilbert functions and H^0 of T(k) ⊗ I_Z.

**Evidence a referee would accept.** (a) every identity used re-checked
by one script at random rational points; (b) finite certificates by
two independent code paths (raw path matrix vs quotient R_n);
(c) a fresh-subagent review of the final proof, recorded.

## 3. Routes tried and why they failed (19 Oct 2026)

All finite computations below are exact (fmpq or F_p with p = 2^61-1) at
product-form points; l-adic valuations use epsilon = l = 10007 (1009 as a
second prime). They are evidence, not proofs.

* **Full rank, evidence.** det R_n != 0 at a genuine economic point
  (random g, u_t = (1,3,7)^t) for every n <= 8, i.e. T <= 10
  (hq_fresh_fast.py).
* **Route 1, newest-block torus degeneration: KILLED.** Only the vertex
  direction (new lines concurrent at a coordinate vertex) keeps
  v(det R_{n+1}) = 0, and only for n <= 3. Smith exponents of R_{n+1}(eps)
  are -1^(3n), 0^(...), 1^(3n + 9n(n-3)/2): the defect is exactly
  9n(n-3)/2 = (old cross pairs) - 9n, since Gamma loses one rank per old
  cross pair and the new block can repair at most 9n. All exponents lie
  in {-1,0,1} (first-order jets suffice), but the first-order map is as
  large as the problem (hq_fresh_newest_degen.py, hq_fresh_smith.py).
* **Global degenerations: KILLED at leading order.** Smith defects for
  n = 3,4,5: persistence G = D + eps H: 30, 63, 117; weak state dependence
  G = (c_i) + eps H: 30, 73, 185; staircases u_t = eps^{x_t (0,1,2)}: hundreds;
  vertex-cycling blocks: 0, 17, 52 (hq_fresh_global_degen.py).
* **Single dominant term: KILLED.** At random tropical points the min-cost
  matching value of the valuation matrix of R_3 is strictly below
  v(det R_3) in 28/30 trials (hq_fresh_tropical.py): canonical coordinates
  cancel tropically.
* **Route 3, intrinsic head map: KILLED.** Lambda_n = (head sums) o R_n^{-1}
  is 100% dense at n = 4, 5, both in canonical and in standard-tail
  coordinates.
* **Transverse residue tau on the new lines** has rank exactly 9n on the 18n
  new columns (3n per new line), n = 2..5; T_n - I is dense in all 9x9
  blocks. So no shortcut through tau alone.

## 4. Theorem A: a basis closed under appending (PROVED)

Notation: blocks 0..n-1 in time order; for t != r put
K_{>r} := prod_{u > r, u != t, increasing} K_u (empty product = I) and

    G_{t,r,a,b} := B_{t,r,a,b} K_{>r} = h_{tab}(I - K_r) K_{>r},   h_{tab} = X_a K_t(a,b) e_b.

**Theorem A.** On the geometric open set of the product-form family,
{E_{s,a}} ∪ {G_{t,r,a,b}} is a basis of W_n for every n >= 1, and in
canonical coordinates
det R^G_{n+1} = det Gamma_n · det R^G_n · prod_{u<n, c, d} kappa_{u,c,d}, with
kappa_{u,c,d} = [(v_uc(P) K_{>u}(P)) ∧ v_nd(P)] / [v_uc(P) ∧ v_nd(P)],
P = L_uc ∩ L_nd, Gamma_n = prod over old cross pairs of det K_n(P).

*Proof.* (i) Membership: W_S K_u ⊂ W_{S ∪ {u}} for a block u not in S (the
new numerators vanish at the new block's six base points and keep the
old base-point zeros), and W_S ⊂ W_{S'} for S ⊂ S'; so G ∈ W_n.
(ii) Appending block n (latest): for old t, r the tail gains K_n as its
last factor, so G^{(n+1)}_{t,r} = G^{(n)}_{t,r} K_n exactly; the new members
are G_{t,n} = B_{t,n} (empty tail) and G_{n,r} = B_{n,r} K_{>r}.
(iii) Canonical coordinates (rows old | N_h | N_s): G K_n has rows
(Gamma R^G_n | 0 | *) by (A1), (A2); B_{t,n} is a canonical basis vector
(a unit vector on the N_s rows); B_{n,r,d,b} K_{>r} has a double pole at
P = L_uc ∩ L_nd only if u = r (row c = b of K_r) or u > r (u in the tail).
So its N_h block is lower triangular in (u >= r) and the diagonal block
u = r is diag over c of kappa_{u,c,d} (normalisations cancel). Eliminating
the N_s rows with the unit columns leaves the block upper-triangular
matrix [[Gamma R^G_n, *],[0, N_h]], giving the product formula.
(iv) Nonvanishing: Gamma_n != 0 on the geometric open set. For kappa, fix
the old blocks and a point P on L_uc; as u_n ranges over the torus,
L_nd = l_d ∘ u_n ranges over all lines with nonzero coefficients, so
v_nd(P) ranges over all zero-sum directions; choosing one not parallel
to v_uc(P) nor to v_uc(P)K_{>u}(P) (nonzero, K_{>u}(P) invertible) gives
kappa != 0. A product of nonzero rational functions on the irreducible
parameter space is nonzero. Induction from R^G_1 (empty) completes it. ∎

EXACT-CHECKED: hq_fresh_standard_tail.py verifies the ratio is exactly 1
and the triangular/diagonal N_h structure for 1..4 old blocks.

### 4.1 Consequence for the equation-(24) family

det R_n = det R^G_n · det C_n where C_n expresses F in the basis G ∪ E.
det R^G_n is a product of explicit nonzero factors, so **L5 is equivalent
to det C_n != 0**, and the irreducible 86-100 digit factor of det R_3 lives
in det C_n. C_n is 35-54% dense for n = 3..5 (no naive triangularity).

### 4.2 Right expansion of F

Write the non-head blocks in order o_1 < ... < o_{n-1}. Then
F_{t,o_i} = sum_{j >= i} G_{t,o_j} + h K_{o_i}(I - K_{o_1} ... K_{o_{i-1}}) K_{>o_i}:
the first word-vector of the equation-(24) column is a standard-tail sum,
the remainder carries a length-two head (t, o_i) and the earlier blocks.

### 4.3 Multiplication operators (PROVED, elementary)

For a block u and states c, d put mu^u_{cd} := multiplication by the scalar
A_u(c,d) X_c / L_{uc}. *Lemma M:* if u is not in S then mu^u_{cd}(W_S) is
contained in W_{S ∪ {u}} (the numerators acquire L_{uc'} L_{uc''} and X_c, which
vanish at the six base points of block u; old base-point zeros persist; the
coordinate syzygy is preserved). With V_b(W) := X_b e_b (I - W):

* B_{t,s,a,b} = mu^t_{ab}(E_{s,b});  G_{t,r,a,b} = mu^t_{ab}(E_{r,b} K_{>r});
* **F_{t,s,a,b} = mu^t_{ab}(J^{[n]-t}_{s,b})**, where J^{[n]-t}_{s,b} = V_b(K_s P) is
  the j = 0 source column of the subsystem without block t
  (and J^S_{s,b} = E_{s,b} + sum_d mu^s_{bd}(J^{S-s}_{min,d})).

Since mu^t_{ab} = A_t(a,b) mu^t_a with mu^t_a = multiplication by X_a/L_{ta}, every
family above is span(E) + sum_{t,a} mu^t_a(X_t) for a 3(n-1)-dimensional input
space X_t inside W_{[n]-t}: X_t = span E_{.,.} (canonical basis), span E K_{>.} (G),
or the j = 0 span J_t of the subsystem (equation 24). **L5 is the statement that
(J_t)_t is admissible**: W_n = span(E) ⊕ ⊕_{t,a} mu^t_a(J_t).

### 4.4 Word families (EXACT-CHECKED evidence, a conjecture)

hq_fresh_words.py builds any family h_{tab}(I - W_{t,j}). Full rank (mod p) for:
DHW, s+decreasing, rest-then-s, random full orders, B (s alone), s+one letter,
"omit s" words, n = 3..6. *All* 216 families with two distinct words per head
group at n = 3, and 60 random distinct-word families at n = 4, 5, are bases;
failures occur only when two words of one head group coincide. Conjecture GW:
any n-1 pairwise distinct words per head group give a basis. (Per-(t,a,b)
independent choices fail occasionally: 2/80 at n = 3.) All word vectors with
one head are independent (64 of them at n = 5), so there is no per-head
direct-sum decomposition behind this.

### 4.5 Degenerations of C_n (EXACT-CHECKED)

Smith sums (R^G, R^F, C) along degenerations, n = 3 | 4: persistence
G = D + eps H: (0, 30, 30) | (0, 63, 63) -- the standard-tail basis stays
nondegenerate, all defect is in C_n; weak dependence: (27,30,3) | (108,73,-35);
newest vertex: (9,0,-9) | (27,0,-27). C_n has mixed signs elsewhere.

### 4.6 Further killed routes (20 Oct 2026, early)

* **Concurrency (beta_1 = beta_2: all lines of colour a through one point):**
  canonical Smith exponents look mild, but the E/F functions at the exactly
  concurrent point have rank defect 2, 7, 16, 28, 42, 58 (n = 2..7): killed.
* **Function-evaluation screen** (intrinsic, no coordinates): self-similar
  economic points u_t = lambda^t, geometric subgroup u_t = (1, s_t, s_t^2),
  S_3-symmetric G = J + cI, symmetric G: all full rank for n <= 7. These give
  structured base points but no proof; on the geometric (one conic per colour)
  subfamily det R_3 still has a 67-72 digit cofactor (no product formula).
* **One DHW head group, the others canonical:** det = prod_a det D_{t,a}
  (a 3(n-1)-square collocation of the subsystem's j=0 residues at the
  crossings with L_ta) already has a 50-53 digit cofactor at n = 3.
* **No multiplicative recursion:** the large cofactors of det R_3, det R_4,
  det R_5 at nested configurations are pairwise coprime (det S_n carries
  det R_n in its denominator).
* **Signs:** det R_n and det R^G_n both change sign on the positive domain
  (canonical normalisation has poles/zeros there); positivity not usable here.
* **Differential Horace at the newest vertex:** the order-1 map on the
  9n(n-3)/2-dimensional kernel again contains the head map Lambda_n.

### 4.7 The head map has an explicit kernel; the exact step map (PROVED + EXACT-CHECKED)

Lambda_n(w) := head sums of the source-family coefficients of w minus the
E-coefficient spread. Since J_{s,b} = E_{s,b} + sum_d F_{s,r0,b,d} (the j = 0
reduction), Lambda_n(J_{s,b}) = 0; headless differences F_{t,s,a,b} - F_{t,s',a,b}
are killed too, and a dimension count gives

    ker Lambda_n = span{F_{t,s,a,b} - F_{t,s',a,b}}  ⊕  span{J_{s,b}}   (dim 9n^2 - 15n).

Appending the latest block N: the old part of the (n+1)-family spans
Phi_n(W_n) ⊕ span(E_N) with Phi_n(w) = w K_N + sum_{tab} Lambda_n(w)_{tab} B_{t,N,a,b},
i.e. (ker Lambda_n) K_N ⊕ span{h_{tab}(I - Pi_(t) K_N)}. The old-head new columns
reduce to commutators: F_{t,N,a,b} - F'_{t,s_min,a,b} = h_{tab}[Pi_(t), K_N], and
sum_b F_{N,s,a,b} = J_{s,a} K_N + X_a e_a [W_s, K_N]. In the basis
{F_k K_N, B_{t,N}, B_{N,r} K_{>r}} of W_{n+1}/E (Theorem A), the induction step is
exactly: T(gamma) = beta(gamma) - Hd·alpha(gamma) is invertible on the
9n-dimensional tau-kernel B0 of the new columns (hq_fresh_step_map.py: rank
T = 9n for n = 2..5; Hd·alpha has full rank 9n too, so the step is not
Lambda-free; T is dense across new-line sectors for n >= 4).

**Structural conclusion.** Every inductive route found so far needs the
previous level's head map Lambda_n (head sums of the source-family
expansion). An induction must therefore carry an invariant about Lambda_n,
or bypass it by a degeneration in which the new columns' old parts vanish
while Gamma stays invertible (none exists within the torus).

## 6. General Q (side results)

### 6.1 T = 4, every Q >= 3: independence (PROVED)

**Proposition.** For every Q >= 3 and every initial outcome, the ell(Q,4) =
3Q^2 + 2Q moments of (24) are linearly independent for parameters in an open
dense subset of the economic domain.

*Proof.* (i) Split: at T = 4 only j in {0,1} occur and, for Q >= 3, the j = 1
shared position is unrestricted; the columns with shared position 1 are Q
disjoint indicator lifts of the T = 3 family (Q moments), independent by
DHW Proposition 2 (generic x, beta). (ii) Quotient: the conditional-sum map
C_i(m) = sum_{y_1 = i} m(y) p_y kills the lifts, and telescoping the transformed
chain gives, up to the nonzero column factor K_1(y0, a), the images
X_a e_a (I - K_s K_r) (j = 0) and X_a K_t(a,b) e_b (I - K_s) = B_{t,s,a,b} (j = 1),
with blocks {2,3}; the constant column operation of sec. 0.1 turns the j = 0
images into E_{s,a}. (iii) Independence of {E_{s,a}} ∪ {B_{t,s,a,b}} in P^{Q-1}:
multiply a relation by L_ta L_sb and restrict to the codimension-2 subspace
H_ta ∩ H_sb; only B_{t,s,a,b} and B_{s,t,b,a} survive, with values
-A_t(a,b) X_a X_b v_sb and -A_s(b,a) X_a X_b v_ta. These are independent vector
functions there because A_s(b,.) and A_t(a,.) are not proportional and no X_i
vanishes identically on the subspace (open conditions, nonempty on the economic
domain), so both coefficients vanish. Single residues -X_a v_sa along H_sa then
kill the E coefficients. (iv) A relation among all T = 4 columns maps to a
relation among new images, so the new coefficients vanish; the remaining
relation among the disjoint lifts vanishes by (i). ∎

EXACT-CHECKED: hq_fresh_generalQ_quotient.py verifies the quotient images for
Q = 3, 4 at T = 4, 5 (24, 40, 63, 108 identities by brute-force path sums);
hq_fresh_generalQ.py finds full raw rank at economic points for Q = 3..6
(T = 4) and Q = 4 (T = 5). *Not proved:* spanning for Q >= 4 (needs the
dimension dim M_4 = ell(Q,4), the second half of DHW Conjecture 1, known only
for Q = 2 and, in this project, Q = 3). For Q >= 4 and T >= 5, new columns with
j >= 2 (double heads mu^{t1} mu^{t2}) appear.

### 6.2 Finite certificate, Q = 3 (EXACT-CHECKED)

hq_fresh_certificate.py: det R_n != 0 mod 2^61-1 at one genuine economic point
for n = 2..12, so the equation-(24) family is a generic basis for every
T <= 14 (finite result; raw T = 7 matrix also full rank, 2013 x 2187).

## 5. Remaining obstruction

det C_n != 0 for all n (equivalently L5, equivalently admissibility of (J_t)).

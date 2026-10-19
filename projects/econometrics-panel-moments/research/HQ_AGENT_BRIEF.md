# Brief: the remaining determinant (self-contained, 20 Oct 2026)

## Objects (Q = 3 states {0,1,2}, n blocks = time-ordered transitions)

* Block t has a 3x3 matrix A_t; lines L_ta(X) = sum_i A_t(a,i) X_i on P^2,
  X = (X_0,X_1,X_2). Kernel K_t(X) = diag(L_t)^{-1} A_t diag(X) (row stochastic).
* **Product form (the economic case):** A_t(a,i) = g(i,a) u_t(i) with ONE common
  positive 3x3 matrix g and torus elements u_t. All blocks are torus translates
  of one block. (Economic genericity reduces to: det != 0 at ONE point of this
  product-form family, for each n.)
* Row vectors. h_tab := X_a K_t(a,b) e_b. For a word W (product of distinct K_u,
  u != t, in some order) the *word vector* is h_tab (I - W).
* E_{s,a} := X_a e_a (I - K_s);  B_{t,s,a,b} := h_tab (I - K_s)  (t != s).
* **Source family (equation 24 of Dano-Honore-Weidner, quotient form):**
  F_{t,s,a,b} := h_tab (I - W_{t,s}),  W_{t,s} = K_s * (all other blocks except s,t,
  in increasing time order).
* W_n := the 3n(3n-2)-dimensional space of zero-sum rational vector functions
  (X_i g_i / D) with g_i in I(Z)_{3n}, D = product of the 3n lines, Z = the six
  base points of each block (within-block line intersections and
  L_ta ∩ {X_a = 0}). {E} ∪ {B} is a basis ("canonical basis"); the B-coordinates
  of a vector are read off from double residues at the cross points
  L_ta ∩ L_sb (t != s), in the basis (v_ta(P), v_sb(P)), v_ta = (A_t(a,i) X_i)_i.

**THE GOAL:** for every n, {E} ∪ {F_{t,s,a,b}} is a basis of W_n at some
product-form point (equivalently det R_n != 0, R_n = B-coordinates of the F's).
Verified numerically mod p for n <= 8. A proof for all n is wanted.

## What is proved (use freely)

* (L4) Appending the latest block N: every old column becomes
  F' = F K_N + B_{t,N,a,b}; at old cross points rho_P(F') = rho_P(F) K_N(P); at new
  cross points the double residue of F' is a multiple of v_Nd(P).
* (Theorem A) G_{t,r,a,b} := B_{t,r,a,b} K_{>r} (K_{>r} = increasing product of the
  blocks u > r, u != t) together with E is a basis of W_n for all n, and
  det R^G_{n+1} = det Gamma * det R^G_n * prod kappa_{u,c,d} exactly, with
  Gamma = prod over old cross points of det K_N(P) and
  kappa = [(v_uc(P) K_{>u}(P)) ∧ v_Nd(P)] / [v_uc(P) ∧ v_Nd(P)], P = L_uc ∩ L_Nd.
  Reason: G appends exactly (G K_N), B_{t,N} are canonical unit vectors, and
  B_{N,r} K_{>r} has block-triangular transverse residues.
* (Multiplication form) mu^t_{ab} := multiplication by A_t(a,b) X_a / L_ta maps
  W_S into W_{S∪{t}}. F_{t,s,a,b} = mu^t_{ab}(J_{s,b}) with J_{s,b} = X_b e_b (I - K_s P)
  the j = 0 column of the subsystem without t.
* (Head map) Lambda_n(w) := head sums of the F-coefficients of w (minus E-spread).
  ker Lambda_n = span{F_{t,s,a,b} - F_{t,s',a,b}} ⊕ span{J_{s,b}}. Every inductive
  step found needs Lambda_n of the previous level: the step is the invertibility of
  a 9n x 9n map T = beta - Lambda_n o w' on the 9n-dim space of new-column
  combinations with longitudinal new-line residues (hq_fresh_step_map.py).

## Killed (do not repeat without a new reason)

Torus degenerations of the newest block (defect exactly 9n(n-3)/2), all global
degenerations tried (persistence G -> diagonal, weak dependence, staircases,
vertex cycling, concurrency beta_1 = beta_2), single dominant tropical term,
head map locality (Lambda_n is 100% dense in both canonical and G coordinates),
positivity of det in canonical coordinates, multiplicative recursion (cofactors
of det R_3, R_4, R_5 are coprime), product formulas on structured subfamilies.

## Evidence and leads

* **Word-family phenomenon (Conjecture GW):** replacing the DHW words by ANY n-1
  pairwise distinct words per head block t (same set for all (a,b)) still gives a
  basis: all 216 such families at n = 3, 60 random ones at n = 4, 5 (only equal
  words fail). All word vectors with one head are independent (64 at n = 5).
* det R_3 is a perfect cube Phi^3 times natural factors (n = 3 only).
* In the persistence limit G = D + eps H the standard-tail lattice is exactly
  nondegenerate while DHW has Smith exponents in {0,1,2} (Lie-algebra limit:
  K_u = I + eps N_u, word differences become commutators).

## Tools

Python venv: `math/.venv/bin/python` (python-flint 0.9, sympy, numpy, scipy).
Directory `projects/econometrics-panel-moments/exploration/`:
* `hq_fresh_fast.py`: `Ring(p)` (p=None for exact fmpq), `product_blocks`,
  `build_R`, `R_matrix`, `geometry_ok`, `kernel_at`, `word_product`.
* `hq_fresh_words.py`: `build_cols(A, n, R, columns)` gives canonical B-coordinates
  of arbitrary word-vector combinations; `F_columns`, `G_columns`.
* `hq_fresh_standard_tail.py`, `hq_fresh_step_map.py`, `hq_fresh_smith.py`
  (l-adic Smith exponents), `hq_fresh_newest_degen.py`, `hq_fresh_univariate.py`.
Notes: `research/HQ_FRESH_APPROACH.md` (full record).

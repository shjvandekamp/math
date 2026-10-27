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

* **Word families:** Conjecture GW (any distinct words) is REFUTED at n = 4; the
  surviving form GW-Hall (n-1 distinct words per head satisfying Hall's condition)
  is checked for n <= 8 (AGENT_LIE_NOTES.md). DHW satisfies Hall.
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

## Updates (20 Oct 2026, late) -- read these too

* **Module picture.** W_n = ⊕_{s,b} S_s E_{s,b} uniquely, S_s = span{1, X_a/L_ta : t != s}.
* **Lambda-free filtration.** V_m := W_{<=m} Pi_{>m} (right multiplication by the increasing
  product of blocks > m); W_{n+1} = W_n K_N ⊕ E_N ⊕ span{B_{t,N}} ⊕ span{B_{N,s}}.
  With s_min(t) = min([n] - t): D_{t,s} := F_{t,s} - F_{t,s_min(t)} lies in V_{max(t,s)} and
  appends exactly (D K_N); I_t := F_{t,s_min(t)} = h_tab(I - Pi_(t)) = sum_r G_{t,r} sits in the
  top piece. DHW ≡ {E} ∪ {D} ∪ {I}; all difficulty is in the 9n vectors I (= Lambda).
* **Collision leads (AGENT_AG_NOTES.md sec. 5 and new):**
  - latest pair u_N = u_{N-1}(1 + delta nu): intrinsic Smith exponents only 0, 1 with
    18m - 24 ones (= coinciding family pairs);
  - NEW: newest with OLDEST, u_N = u_0 (1 + delta nu): intrinsic Smith exponents of the
    E/F evaluation matrix are 0:105, 1:15 (n=4), 0:183, 1:12 (n=5), 0:274, 1:12 (n=6),
    i.e. a BOUNDED defect 12 = the forced coincidences F_{N,0} = F_{0,N} (9) and
    E_N = E_0 (3). At exact coincidence u_N = u_k (k <= N-3) the rank deficit is 12 too.
    The canonical B family is much more degenerate there (18m - 24 ones), so canonical
    coordinates blow up (v(det R_n) = -33, -54, -72).
* **No product formulas anywhere:** persistence leading coefficient at n = 4 has irreducible
  factors of degrees 4, 14, 21, 26 (along u_3(1)); shift-invariant points u_t = lam^(t+1)
  give degree 154 at n = 4; collision leading coefficient / det R_{m-1} has degree-88 factors.
* Scripts added: hq_fresh_nearperm.py, hq_fresh_geom_factor.py; the intrinsic test is
  hq_fresh_coalesce.family_eval (evaluate E/F or B/G family at fixed points) + hq_fresh_smith.

## Updates (21 Oct 2026) -- the "room" picture (read this)

* For general Q the quotient images of the new (24) columns are N(H, q_H; s, q0) = (prod_{u in H} X_{q_u}/L_{u q_u}) J^R_{s,q0}
  (H = head blocks, R = the rest, s in R, J^R the j = 0 column of R). They are UNITRIANGULAR over the canonical
  multi-heads C(H; s) = (prod_H mu) E_{s,q0} (expand J along its increasing word: each letter becomes a new head).
  When n <= Q - 1 the canonical multi-heads are independent (iterated residues at codimension-(|H|+1) strata), so
  DHW Conjecture 1 holds for all T <= Q + 1 (research/GENERALQ_PROOF.md, notes secs. 6.5-6.6).
* For Q = 3 the strata of codimension >= 3 are empty: the multi-heads with >= 2 heads COLLAPSE (partial fractions on
  P^2) onto the E/B basis. R_n = I + (collapsed higher-head terms of F_{t,s} = B + sum_d mu^t mu^s (increasing column
  of the rest)). This collapse is the whole difficulty; R_n - I has full rank (n = 3..6).
* Oldest-newest collision (research/AGENT_COL_NOTES.md): P(n) <== Q_cyc(n-1) with a local, proved 12-jet step;
  Q_cyc still contains a 9m x 9m Lambda-twisted step; S_0 is independent of the middle-block order (CONJECTURE I).

## Updates (27 Oct 2026) -- the canonical basis (read this first)

* **The canonical family is a basis for every n (PROVED, reviewed; research/GENERALQ_ALLT_PROOF.md).**
  Keep DHW's index set (24)-(25) but take the generation orders (t, s1, s2, r, T), (t, s2, s1, r, T)
  instead of DHW's (t, s1, r, s2, T), (t, s2, r, s1, T). These are valid moments (DHW's Theorem 1). Their
  new-column images are exactly the canonical E_{s,a}, B_{t,s,a,b} (up to nonzero constants). So the canonical
  basis {E} ∪ {B} of W_n comes from actual moments, and these moments are a basis of M_T for every T.
* Hence L5 is literally "DHW's columns are invertible in the canonical basis": det R_n != 0. Nothing else
  of DHW's Conjecture 1 for Q = 3 is open. (For general Q: the count dim M_T = ell(Q,T) holds for every T; the
  analogous matrix is unitriangular for T <= Q+1 and dense for T > Q+1.)
* **Spanning of W_n by {E, B} now has a direct proof** (descending iterated residues: cross points, then lines,
  then level 0), not via the dimension count.
* **Do not use common-conic points as witnesses.** At points where all 3n lines are tangent to one conic, e.g. the
  general-Q witness g(j,r) = w_r^(j-1), u_t(j) = z_t^(j-1), R_3 has rank 51/54 (the non-lift matrix 60/63). The
  symmetric conic points g = (1-eps)I + eps J, u_t = (1, z_t, z_t^2) also drop rank. R_4 is nonsingular there, but
  the n = 3 deficit propagates to all T >= 5 through the lifts.
* Killed on 27 Oct (see HQ_FRESH_APPROACH.md sec. 4.16):
  - the persistence leading coefficient (no product formula; factors of degree 14, 21, 26 at n = 4);
  - families interpolating between canonical and DHW words (each has its own irreducible factors);
  - dense multi-head relations;
  - no order-free subspaces;
  - the Q' >= T-1 embedding (it only gives the unrestricted family).

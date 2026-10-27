# E1 induction step in the persistence limit (agent PER2, from 23 Oct 2026; written as it goes)

Continuation of research/AGENT_PER_NOTES.md (sec. 4.14 of HQ_FRESH_APPROACH.md). Notation as
there:
* normalised canonical lattice L_B' = span{eta, beta};
* standard-tail lattice L_G' = L_B';
* normalised DHW lattice L_F';
* normalised head map Lambda' = n_ab Lambda, with n_aa = -eps, n_ab = -eps^2 c_tab.

Labels: PROVED, EXACT-CHECKED (mod P = 1073741789 at one random product-form point, eps a
formal variable, method in each script), CONJECTURE, REFUTED.

Scripts (exploration/, run with ../../../.venv/bin/python):

| script | content |
|---|---|
| agent_per2_lib.py | coordinates mod eps^r in a lattice basis: block-Toeplitz rref (coords_mod) and the memory-light peeling through the tracked saturated basis (coords_peel); they agree exactly at m = 4 |
| agent_per2_headmap0.py | Lambda'_n(0) on all generators of L_B', L_G'; (*) and (**); support / density (n = 4, 5, 6; 2-25 s each) |
| agent_per2_step.py | the 18n x 18n step: dim T, target basis, K0, ranks of both parts, coverage (m = 5, 6, 7; 4-35 s) |
| agent_per2_stepstruct.py | valuation filtration F_k, levels of T and of the two parts, filtered-splitting test (m = 5, 6, 7; 8 s - 1.5 min) |
| agent_per2_lamlevels.py | rank of Lambda'_n(0) and of E-sums on each F_k (n = 4, 5, 6; up to 50 s) |
| agent_per2_explicit.py | explicit part X = Im Psi_0^(n), the excess of the new columns' old components and its levels (m = 5, 6, 7; up to 1 min) |

## 0. The step, precisely (PROVED reformulation)

Setting:
* m = n + 1 blocks, N = newest, S = old blocks.
* L1 = span{eta_all, F'_{t,s} : t, s in S}. These are the appended old columns
  Phi_n(L_F'^(n)) plus eta_N.
* V = span of the 18n new columns F'_{t,N,a,b}, F'_{N,s,a,b}.
* M = L_B'^(m) / (L1 + eps^2 L_B'^(m)), and T = (eps L_B' + L1 + eps^2 L_B')/(L1 + eps^2 L_B') ⊆ M.
* M_0 = M/T = L_B'/(eps L_B' + L1).
* K0 = {v in V : [v] = 0 in M_0}.

By Krull (AGENT_PER_NOTES 4.3), E1(m) <=> T ⊆ (span_C V + eps span_C V) mod (L1 + eps^2 L_B').
Elements of that image lying in T are [k] (k in K0) and [eps v] (v in V). Also
[eps v] = pi([v]_{M_0}), where pi = multiplication by eps, M_0 -> T. Hence

    E1(m)  <=>  Step : K0 (+) V/K0 --> T,  (k, v) |-> [k] + [eps v]   is onto.

Since dim K0 + dim V/K0 = 18n, Step is a square 18n x 18n map whenever dim T = 18n.
* Given E1(n) and (*)(n), T is spanned by the classes of eps B'_{t,N} and eps G'_{N,r}
  (AGENT_PER_NOTES sec. 6).
* The old classes reduce as eps x K_N == -eps sum_tab Lambda'_n(x)(0)_tab B'_{t,N,a,b}.
  This is the only place where the old system enters.

## 1. Intermediate findings (23 Oct, written as they come)

**1.1 Leading head map (task 2) and condition (**) (task 3).** EXACT-CHECKED,
agent_per2_headmap0.py, n = 4, 5, 6. Lambda'_n(x)(0) is computed for all generators x of
L_B'^(n) and L_G'^(n) from the F'/eta-coordinates of eps*x mod eps^2.
* (*) holds: the order-0 head sums vanish.
* (**) holds: the E-coefficient sums vanish mod eps.
* The eta columns are explicit: Lambda'(eta_sa)(0) = -e_(s,a,a).
* Every beta- and G'-column has FULL support: all 9n heads are hit.
  * Density is 0.90, 0.93, 0.94 and the rank is 9n.
  * On G'_{t,r,a,b} the own-head entry is not even constant in (a,b).
* Verdict: in the natural generators of L_B'/L_G', the leading head map is as dense as the
  generic one. Kill criterion half met (see 1.3 for the part that matters).

**1.2 The step at m = 5 (n = 4).** EXACT-CHECKED, agent_per2_step.py, seed 101.
* dim T = 72 = 18n, and the classes eps B'_{t,N}, eps G'_{N,r} form a basis of T.
* rank S00 = 18 = 3n + 6, and pi is injective on Im S00.
* dim K0 = 54 = 15n - 6, and rank Step(K0) = 54.
* Total rank 72, so the step is invertible and E1(5) holds through the step (consistent
  with AGENT_PER_NOTES).
* Both parts hit both target types: the pi-part has rank 9 on the B'_{t,N} rows and 18 on
  the G'_{N,r} rows; the K0-part has rank 36 on each.
* So there is no block separation by target type.

**1.3 The step versus the pole-order filtration (task 1).** EXACT-CHECKED,
agent_per2_stepstruct.py, seed 101.

Definitions:
* F_k ⊆ L_G'^(m)/eps L_G'^(m) is the set of constant coefficients of elements of
  valuation >= k. Its dimensions are d - dim Pi_{k-1}, checked.
* T_k = class of eps F_k in T.

| m (n) | dim T_k, k = 0.. | gr_k T at levels | rank S00 | dim K0 |
|---|---|---|---|---|
| 5 (4) | 72, 72, 72, 72, 72, 60, 30, 6, 0 | 12, 30, 24, 6 at levels 4, 5, 6, 7 | 18 = 3n + 6 | 54 = 15n - 6 |
| 6 (5) | 90 (k <= 5), 75, 54, 24, 0 | 15, 21, 30, 24 at levels 5, 6, 7, 8 | 21 = 3n + 6 | 69 = 15n - 6 |

* So T sits at the TOP of the pole-order filtration. gr_k T = gr_k Pi^(m) is the complete
  graded piece for k >= 5 when m = 5, and for k >= 7 when m = 6.
  * The lower levels are partial: at m = 5, level 4 has 12 of 39; at m = 6, level 6 has
    21 of 36 and level 5 has 15 of 48.
* In the m = 5 system these top pieces are exactly the "delayed" parts
  gr_k Pi - sigma_k = 30, 24, 6 at k = 5, 6, 7 (AGENT_PER_NOTES 4.5).
* The step must therefore produce, at first order, the whole top of the m-system.
* Natural two-part source: P = eps * (order-0 image of the new columns) and
  Kp = Step(K0). Its levels:
  * m = 5: P ∩ T_k has dims 18 (k <= 4), 6, 0. Kp ∩ T_k has dims 54, 42, 12, 0 (k = 4..7).
  * m = 6: P reaches level 6 only. Kp ∩ T_8 has dim 3, while dim T_8 = 24.
* Hence T_k ≠ (P ∩ T_k) (+) (Kp ∩ T_k) at the top levels. REFUTED: the step is not
  triangular for the pole-order filtration with respect to its natural source split. The
  top target levels arise only from cancellations between order-0 images of new columns and
  first-order parts of K0-combinations.
* The preimage filtration makes any isomorphism triangular, so that is no content. The
  diagonal blocks (sizes 12, 30, 24, 6 and 15, 21, 30, 24) are the "delayed symbols" of
  the new block, with no explicit description found.

**1.4 The step at m = 7 (n = 6).** EXACT-CHECKED, agent_per2_step / agent_per2_stepstruct,
seed 101.
* dim T = 108 = 18n, and the target classes form a basis of T.
* dim K0 = 84 = 15n - 6; rank S00 = 24 = 3n + 6; pi is injective on Im S00.
* Total rank 108, so the step is invertible.
* T levels: dim T_k = 108 (k <= 6), 90, 84, 48, 18, 0. Hence gr_k T = 18, 6, 36, 30, 18 at
  levels 6..10.
* Levels 8, 9, 10 are the complete graded pieces gr_k Pi^(7) (36, 30, 18). Levels 6, 7 are
  partial (18 of 57, 6 of 42).
* The natural split is again not filtered: P ∩ T_8 = 0 and Kp ∩ T_10 = 0, although
  dim T_10 = 18.

Summary of the step invariants, n = 4, 5, 6 (CONJECTURE for all n >= 4):
* dim T = 18n;
* rank S00 = 3n + 6;
* dim K0 = 15n - 6;
* pi is injective on Im S00;
* Step(K0) has rank 15n - 6, complementary to pi(Im S00);
* T contains the complete top graded pieces gr_k Pi^(n+1) for all k >= k_0, with
  k_0 = 5, 7, 8 for m = 5, 6, 7.

**1.5 Lambda'_n(0) along the valuation filtration (task 2).** EXACT-CHECKED,
agent_per2_lamlevels.py.
* rank(Lambda'_n(0) restricted to F_k^(n)) = min(9n, dim F_k) at EVERY level k, for
  n = 4, 5, 6.
  * n = 4: Lambda'(0) is an isomorphism F_4 -> C^36.
  * n = 6: Lambda'(0) is an isomorphism F_7 -> C^54.
  * It is injective on all higher F_k.
* The first-order E-coefficient sums have rank 3 on every F_k.
* So Lambda'_n(0) behaves like a generic map at every pole-order level; no vanishing or
  selection was found. KILLED: "Lambda'_n(0) is explicit (letter sets, commutator classes,
  Laurent coefficients)" in all forms tested. Since it is generic, no closed form of the step
  matrix through Lambda' was attempted.

**1.6 How much of Lambda'_n(0) the step actually needs (task 2, refined).** EXACT-CHECKED,
agent_per2_explicit.py.

PROVED (from the definitions):
* The denominator Z1 contains the graph {(b, Lambda'_n(b)(0)) : b in L_B'^(n)} over the old
  coordinates. In target coordinates, Step = (new-label components) - twist(old components).
* The twist is explicit exactly on X = Im Psi_0^(n), the order-0 old components of L1.

EXACT-CHECKED:
* dim X = f(n) = 57, 78, 102 for n = 4, 5, 6.
* The canonical part of the source is the order-0 coordinates of the 18n new columns. Their
  old components exceed X by exactly 3(n-2) = 6, 9, 12 dimensions.
  * Each column type, F'_{t,N} alone or F'_{N,s} alone, gives the same excess space E.
* The level filtration of E in the old system is LOW:
  * n = 4: 3 at level 2 and 3 at level 3;
  * n = 5: 3 at level 2 and 6 at level 3;
  * n = 6: 9 at level 3 and 3 at level 4.
  The top level is 5, 7, 8 respectively.

So the pi-part of the step needs the non-explicit Lambda'_n(0) only on a 3(n-2)-dimensional
low-pole-order subspace (SURVIVES as structure). The K0-part (dimension 15n - 6, the bulk) has
old components that are defined only modulo the full graph. It necessarily uses the old
system's first-order data:
* the first-order G'-coordinates of the appended old DHW columns;
* Lambda'_n(0) off X.

So the induction cannot be carried by E1(n) + (*)(n) alone. It needs the old system's
lattice modulo eps^2 L_B'^(n).

## 2. Propagation of (*) and (**) (task 3)

**2.1 (PROVED, normalised AG 1.2, directly from Phi_n on the basis).** Write
w = sum alpha F'^(n) + sum gamma eta. Then

    Phi_n(w) = sum alpha F'^(m)_old + sum gamma_s (eta_s - eta_N),

so

    Lambda'_{n+1}(Phi_n w)_{tab} = Lambda'_n(w)_{tab}                       (t old)
    Lambda'_{n+1}(Phi_n w)_{N,a,a} = sum_s gamma_{s,a}(w),
    Lambda'_{n+1}(Phi_n w)_{N,a,b} = eps c_{N,a,b} sum_s gamma_{s,a}(w)      (b != a).

The eta-coefficient sums of Phi_n(w) vanish identically.

**2.2 (PROVED).**
* (*)(n) + (**)(n) imply that Lambda'_{n+1} is regular on Phi_n(L_B'^(n)). Here (**)(n)
  says: the eta-coefficient sums of the F'-coordinates of eps x vanish mod eps, for
  x in L_B'^(n).
* (**)(n+1) holds identically on Phi_n(L_B'^(n)).
* L_B'^(n+1) = span{eta_N, Phi_n(L_B'^(n)), B'_{t,N}, G'_{N,r}}. This uses (*)(n) and
  L_G' = L_B'; the latter is EXACT-CHECKED (AGENT_PER_NOTES (I4)).
* Hence (*)(n+1) and (**)(n+1) reduce to their restriction to the 18n new canonical
  generators B'_{t,N}, G'_{N,r}.

**2.3 (EXACT-CHECKED).**
* (**)(n) holds for n = 4, 5, 6 (agent_per2_headmap0).
* (*)(n) holds for n = 4, 5, 6.
* So the new-generator conditions hold at n+1 = 5, 6.

They are first-order conditions on the same 18n new directions as the step and do not
follow from it formally. Propagation is thus done for the old part; the new part has the
same nature as the step itself.

## 3. Verdict, and the most promising next step

**Survived.**
* The step is a clean square problem, with dim T = 18n, rank S00 = 3n + 6 and
  dim K0 = 15n - 6. It is invertible for n = 4, 5, 6 and the invariants are uniform.
* Its target is the top of the pole-order filtration of the (n+1)-system (complete top
  graded pieces).
* The canonical (pi) part needs the old head map only on a 3(n-2)-dimensional low-level
  subspace.
* Propagation of (*) and (**) through the old part is PROVED.

**Killed** (the coordinator's kill criterion is met for this route):
* Lambda'_n(0) is dense and of generic (maximal) rank at every pole-order level
  (n = 4, 5, 6). No closed form exists in letter sets, commutator classes or coefficients.
* The step is not triangular for the pole-order filtration with respect to its natural
  split: order-0 images versus first-order kernel parts.
* The top target levels arise only from cancellations between the two parts. So there are
  no explicitly invertible diagonal blocks.
* The bulk of the step, the K0-part, needs the old system's full first-order data. Hence an
  induction must carry the old lattice modulo eps^2, not a closed-form head map.

**Most promising next step.** Prove the TOP-level part directly in the flat limit W^0 =
W^naive. That is where the step's target is complete, gr_k T = gr_k Pi^(n+1) for
k >= k_0, and the old system contributes nothing there.
* Claim to prove: for k >= k_0, the delayed DHW elements of level k+1 realise the whole
  graded piece gr_k Pi^(n+1).
* That piece lives where the vertex schemes and fixed points P_ta of W^naive act, so the
  claim is an interpolation statement about explicit Laurent vectors.
* If it can be proved for all top levels, the remaining lower part of T has dimension
  12, 36, 24 for n = 4, 5, 6. It is where the old first-order data enters and would be
  the residual induction.

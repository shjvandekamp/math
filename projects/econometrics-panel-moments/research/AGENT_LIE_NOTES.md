# Word families, Hall's condition and the near-identity limit (agent notes, 20 Oct 2026)

Angle: the word-family phenomenon (Conjecture GW of HQ_AGENT_BRIEF.md) and the
near-identity / Lie limit. Every claim is labelled PROVED, EXACT-CHECKED,
CONJECTURE or REFUTED. "EXACT-CHECKED" means exact rational (fmpq) or mod
p = 2^61-1 linear algebra at random product-form points. A full rank mod p at one
admissible F_p point certifies generic full rank for that one family and n. A
rank drop at random points is evidence only, unless a structural zero pattern is
shown. Scripts (run with `../../../.venv/bin/python <script>` from `exploration/`):

| script | content | runtime |
|---|---|---|
| `agent_lie_common.py` | helpers: word families, one-head blocks D_{t,a} | <1 s |
| `agent_lie_gw_hall.py` | (S) support rule, (C) GW counterexample, (G1) Hall, (T) transversal, (H) GW-Hall, (N) non-necessity, (M) mixed DHW/canonical | ~30 s |
| `agent_lie_relations.py` | (R1) Relation C, (R2) per-(t,a,b) failures, (R3) no head-block dominance | ~2 s |
| `agent_lie_persistence.py` | (P1) persistence Smith sums for all n=3 families, (P2) swap identity, (P3) DHW defect | ~6 s |
| `agent_lie_gw1_tropical.py` | tropical leading terms and signs of the one-head DHW block | ~5 s |

## Summary

1. **Conjecture GW is false for n >= 4 (REFUTED, by a structural proof).**
   n = 4: head 0 gets the words (1), (2), (1,2), and the heads 1, 2, 3 get their
   single letters (all words distinct). The nine coordinates (0,3,a,d) vanish on
   every column, so the rank is at most 99 < 108. The rank is exactly 99 at three
   random points. The 216/216 at n = 3 is explained by a fact: at n = 3, any two
   distinct words cover both letters.
2. **The right condition is Hall's condition per head.** A head's words must admit
   a matching letters -> words with letter in word.
   * For the one-head block it is necessary (PROVED) and sufficient for distinct
     words (EXACT-CHECKED).
   * Stronger, for the one-head block: rank = structural rank for every set of
     columns. This is a transversal matroid (CONJECTURE T, EXACT-CHECKED).
3. **CONJECTURE GW-Hall:** n-1 pairwise distinct words per head, with Hall's
   condition for each head, give a basis. It is EXACT-CHECKED for n <= 8. DHW
   words are permutations, so DHW satisfies Hall, and **GW-Hall implies the goal.**
4. Hall per head is *not* necessary in the full problem (other heads can
   compensate). Rank can be below the structural rank because of explicit
   cross-head relations (Relation C).
5. The near-identity (persistence) limit sees only letter sets at first order.
   Defects come from words with equal letter sets and from commutator/cyclic
   coincidences of extended words. DHW is the worst case (defect 30, 63, ...).
   **KILLED** as a leading-term mechanism for DHW (it agrees with the brief), now with
   an explanation.
6. All principal head-block minors of the DHW matrix are nonzero, for every
   head set H and n <= 6. Equivalently, "DHW on H, single letters elsewhere" is a
   basis (EXACT-CHECKED). This invites an induction on heads. Head-block
   dominance fails, though (spectral radius >> 1).

## 1. Conventions

* A column is (t,a,b,w) = h_{tab}(I - W). Here W = K_{x1}...K_{xk}, the letters x_i
  are distinct and different from t, and the **extended word** is x = (t, x1, ..., xk).
  The head t carries the head state a, and x1 receives the state b.
* A row (u,v,c,d) is the coefficient of B_{u,v,c,d}, that is, the v_vd(P)-coordinate
  of the double residue at P = L_uc ∩ L_vd. "First slot" = u.
  M_u := span of the rows with first slot u (dimension 9(n-1)). In the pencil
  picture (sec. 6) this row is the component along L_vd.
* **One-head block** D_{t,a}: it has rows (t,v,a,d) (v != t, all d) and columns
  (b,w), b in {0,1,2}, w a word on S = [n] \ {t}. It is a 3(n-1)-square matrix
  when n-1 words are taken.

## 2. Support rule

**Lemma S.** The coordinate (u,v,c,d) of column (t,a,b,w) is nonzero iff
(i) u, v in x; (ii) u != last(x); (iii) a letter equal to t has state a; and
(iv) if the earlier of u, v is at position 0 and the later at position 1, or the
earlier is at position 1, then the letter at position 1 has state b.

* The *zero* direction is PROVED from the residue formula.
  * There is no pole on the lines of block v unless v ∈ x.
  * The head contributes only row a of K_t, through h_{tab} ∝ X_a e_b / L_ta.
  * With an empty prefix the residue picks (e_b)_c = δ_bc.
  * If u = last(x), the double residue at L_uc ∩ L_vd is a multiple of v_uc(P),
    because nothing follows u. So its v_vd-coordinate is 0.
* The *nonzero* direction is EXACT-CHECKED (generic nonvanishing): 0 mismatches
  in 68,400 entries, n = 3, 4, 5 (`(S)`).

## 3. GW refuted; necessity of Hall (PROVED)

**Proposition N1.** Fix a head t, and give every other head its single letters (s),
which are the canonical B columns, unit vectors at the coordinates (t',s,a',b').
Then the rows with first slot t meet only head-t columns. By Lemma S, the
3|V| rows (t,v,a,·) with v in V are met only by columns whose word meets V.
So the family is a basis only if #{words meeting V} >= |V| for every V ⊂ S,
which is Hall's condition. The counterexample of the summary has V = {3}.
EXACT-CHECKED: the zero rows are exactly the nine (0,3,a,d), and rank = 99 at
3 points (`(C)`).

## 4. The one-head block: Hall and the transversal matroid

* **(G1) Sufficiency of Hall, distinct words** (EXACT-CHECKED, `(G1)`):
  * n = 4: all 455 three-word sets, at 2 points and for all a. The block has full
    rank iff Hall holds (886 full, 24 not Hall).
  * n = 5: 624 sets, including the 24 "covering but not Hall" sets
    {three words on {z,u}} ∪ {(x,y)}. Full rank iff Hall (504 / 120).
  * Also full rank for n = 5, 6 when all words have *identical support*: same
    first and last letter and the same letter set, for example k = 5 words
    (1,σ,5) at n = 6. The same holds when all words are permutations with a
    common first letter.
  * So the phenomenon is **not** "distinct supports". Distinct words with
    identical supports are still independent.
* **CONJECTURE T (transversal matroid).** The column matroid of
  {D_{t,a}[·,(b,w)] : b, w} is the transversal matroid of the supports of
  Lemma S. Equivalently, every square set of columns with a perfect matching in
  the support graph is nonsingular.
  * EXACT-CHECKED (`(T)`): 150 random column sets (mixed b's, words of length
    <= 4) at each n = 4, 5, 6; all 924 six-subsets of the 12 two-letter columns
    {(b,x),(b,y),(b,xy),(b,yx)} at n = 4, 5, 6.
  * Note: a "one generic variable per entry" mechanism cannot explain T. The
    block has 3(n-1) × (many) entries but only ~2n+8 parameters.
* T says, for example, that for a two-letter alphabet *every minor* of the 3x3
  transfer matrix [X_b K_x(b,d)/X_d at P_{y,d}] is nonzero (here P_{y,d} is the point
  L_ta ∩ L_yd). That is a total-nonvanishing statement. It is not a total-
  positivity statement: only 621/1215 entries of D_{0,a} keep their sign across 12
  positive points (`(Sg)`). So naive total positivity fails (REFUTED in that
  naive form).
* Entries factor exactly (PROVED, residue formula). For a row (v,d) and a
  column (b,w) with v ∈ w, put P = P_{v,d}. Then, up to row and column scalars,
  D = P_b [w^{<v}(P)]_{b,d} · β, where β is the L_vd-coefficient (basis
  (L_ta, L_vd) of the pencil at P) of the line Φ_{w^{>v}}(P)(L_vd). Here
  Φ_x(P): X_i ↦ (P_i/L_xi(P)) L_xi is the action of K_x(P) on lines through P
  (zero-sum residues ρ correspond to lines via ρ_i = τ_i P_i). So an entry is
  (prefix transfer) × (suffix transverse factor).

## 5. GW-Hall and cross-head relations

* **CONJECTURE GW-Hall.** It is stated in the summary. EXACT-CHECKED (`(H)`), with
  all families of full rank:
  * n = 4: 60; n = 5: 40; n = 6: 16; n = 7: 12; n = 8: 4 families.
  * The families were random, short-word, common-first-letter permutations, and
    blocks with identical support plus filler.
* **Mixed DHW/canonical** (`(M)`, EXACT-CHECKED): for every H ⊂ [n], DHW words on
  the heads in H and single letters elsewhere give a basis. The counts are
  8/8, 16/16, 32/32, 64/64 for n = 3..6. In canonical coordinates this says:
  every principal head-block submatrix R_DHW[M_H, heads H] is nonsingular. The
  |H| = 1 case is prod_a det D_{t,a}.
* **Hall per head is not necessary in the full problem** (`(N)`). Take balanced
  families where exactly one head violates Hall:
  * 30/40 are bases at n = 4 and 37/40 at n = 5.
  * The rows (t,v,·,·) are then supplied by other heads whose words contain t.
* **Rank < structural rank occurs** (EXACT-CHECKED). n = 4, balanced: head 0 gets
  (2),(3),(2,3); head 1 gets (3,0),(2,3),(0,3); head 2 gets (0,3,1),(1,0),(3,0,1);
  head 3 gets (2),(2,0),(0,2). Rank 102, structural rank 108. Hence no
  "generic support" theorem can hold for the full matrix.
* **Relation C** (EXACT-CHECKED over Q, 3 points, `(R1)`). For t != s, a state a
  and a tail r, the six vectors h_{taa}(I - K_sK_r), h_{saa}(I - K_tK_r),
  h_{tad}(I - K_r), h_{sad}(I - K_r) (d != a) have rank 6 in W/E but rank 5 modulo
  B_{t,s,a,a}, B_{s,t,a,a}.
  * Heuristic source: in h_{taa}K_s - h_{saa}K_t the d = a terms cancel, since the
    scalars K_t(a,a) and K_s(a,a) commute.
  * Per-(t,a,b) word choices fail in 12 of 400 random cases at n = 3, all
    confirmed at 3 further points. 11 failures have a kernel on two heads and one
    head state (Relation C type); 1 has a dense kernel of 48 columns (`(R2)`).
  * This explains the brief's "per-(t,a,b) choices fail occasionally".

## 6. Near-identity (persistence) limit G = D + eps H (Lie structure)

* **Swap identity** (PROVED, elementary; EXACT-CHECKED at 5 rational points, `(P2)`):

      sum_b F(t,a,b, s.R) - sum_b F(s,a,b, t.R) = -X_a e_a [K_t, K_s] R - E_{t,a} + E_{s,a}.

  More generally sum_b h_{tab}(I - W) = V_a(K_t W) - E_{t,a}, with
  V_a(W) := X_a e_a (I - W). So the b-sums of head-t columns depend only on the
  extended word. Two extended words that differ by swapping the first two letters
  give a commutator. For DHW this happens for every pair (t,s): t.s.rest and
  s.t.rest have the same rest.
* **(P1) n = 3, all 216 families × 2 persistence points** (EXACT-CHECKED). These
  are the Smith sums of R(eps), eps = l = 10007.
  * Families with no same-letter-set head: Smith sum 0, except two cases.
    * Each "swap" costs exactly 3 (30/30 family-point cases). A swap means
      head t ⊇ {(s), s.r} and head s ⊇ {(t), t.r}.
    * The 2 cyclic-triple families also cost 3, at both points. Their extended
      words are (0,1,2), (1,2,0), (2,0,1) (or the reverse cycle), each with its
      single-letter partners.
  * Each head whose two words share a letter set costs 9-12.
  * DHW costs 30. Every head of DHW is a same-letter-set pair {uv, vu}.
* **Interpretation.** At first order K_u = I + eps N_u, so a word acts through its
  letter set (abelianisation). Order information enters only at the next order,
  through commutators, and in the degenerate vertex geometry (SOURCE24_NEAR_IDENTITY
  N6) the limiting kernels commute there. All n-1 DHW words of a head share one
  letter set. So DHW is maximally degenerate at first order.
  * DHW Smith sums: 30 (n = 3), 63 (n = 4), max exponent 2 (`(P3)`). The brief
    gives 117 at n = 5. Canonical family: 0.
  * **Kill criterion met:** the leading terms are dependent, with a defect that
    grows with n.
  * The second order is a Lie-type (commutator) computation in a blown-up
    geometry. No evident structure was found. **Sub-route stopped.**

## 7. Other mechanisms tried (all failed or inconclusive)

* **Tropical first-letter dominance for the one-head DHW block** (`(Tr)`). The
  natural diagonal is column (b, w_s) -> row (s,b), the empty prefix.
  * n = 3: optimal and non-cancelling at 3 of 150 random tropical points.
  * n = 4: 0 of 120.
  * Generic non-cancellation is common: 82/150 at n = 3 and 40/120 at n = 4. This
    gives per-n certificates only; no uniform pattern was found.
  * Heuristic reason (not a proof): take a one-letter prefix x and
    b = argmax_i |X_i(P)|. The ratio X_b(P) K_x(P)(b,d)/X_d(P), with d the
    dominant index of L_xb(P), is about X_b/X_d >= 1. So nonempty prefixes cannot
    all be small relative to the empty-prefix diagonal.
* **Head-block dominance** (`(R3)`, KILLED). The block-Jacobi spectral radius
  over heads for DHW, at random positive points, is in [2.7, 159] for n = 3,
  [18, 168] for n = 4 and [51, 1089] for n = 5. So the cross-head blocks dominate.
* **Elementary moves** (PROVED algebra, no leverage).
  * Appending letters in increasing order turns the canonical words into DHW
    words. Stage k is exactly the L4 structure, with block k appended as the last
    factor to columns that do not contain k (the time order plays no role in L4's
    algebra). It therefore reduces to the same Schur complement.
  * The first move from the canonical family, (s) -> (s,x), has a diagonal step
    matrix (PROVED from Lemma S). Its determinant is a product of 9 natural pencil
    factors: the L_sb-coefficients of Φ_x(P)(L_sb), P = L_ta ∩ L_sb.
  * At n = 3 the one-head DHW block is reached in two moves. Its det has a 50-53
    digit cofactor (brief), so the second move carries it.

## 8. Most promising next steps

1. **Replace GW by GW-Hall** in the project record. Any proof must use that each
   head's words cover all other blocks, which DHW does trivially.
2. **Prove Conjecture T** (or only Hall-sufficiency) for the one-head block D_{t,a}.
   It lives on the single line ℓ = L_ta, with the other blocks restricted to it.
   The data are the points P_{v,d} = ℓ ∩ L_vd and the pencil maps Φ_x(P).
   * Candidate tools: degeneration adapted to a chosen matching, at general A
     first. A hand heuristic (not checked): making one block persistent gives
     "last-letter dominance" in that block's rows, which suggests an induction
     deleting a letter that is the last letter of a unique word.
   * Another candidate: a planar-network (Lindström–Gessel–Viennot) model in which
     minors are sums over non-intersecting path systems. That would explain
     "rank = matching number".
3. **Induction on heads via (M).** All principal head-block minors of R_DHW are
   nonzero (n <= 6), and the |H| = 1 blocks are the one-head blocks D_{t,a}. An
   induction H -> H ∪ {t} needs the Schur complement
   R[t,t] - R[t,H] R[H,H]^{-1} R[H,t] to be invertible. A degeneration that makes
   R[t,H] or R[H,t] small for one new head t at a time (not all heads at once,
   which `(R3)` excludes) would reduce the goal to T. This is the most concrete
   new handle found here.

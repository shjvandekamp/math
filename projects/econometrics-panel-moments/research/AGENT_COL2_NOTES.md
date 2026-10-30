# Agent COL2 notes: the delta = 0 space S_0 of the oldest-newest collision, order freedom (21-23 Oct 2026)

Follow-up to research/AGENT_COL_NOTES.md (collision u_N = u_0; S_0 = span of the distinct delta = 0 members of
the cyclic configuration (0, sigma(1..m-1), 0'), m = n-1; Theorem C: P(n) <== Q_cyc(n-1)).
Labels: **PROVED** (argument given), **EXACT-CHECKED** (exact arithmetic mod p = 2^61-1 at random product-form
points; evidence, not proof), **CONJECTURE**, **REFUTED/KILLED**.

| script (exploration/) | content | runtime |
|---|---|---|
| `agent_col2_lib.py` | polynomial numerators g of D_lim f by interpolation, Taylor (jet) functionals, base points, syzygy; self-test | <1 s |
| `agent_col2_sloc.py` | task (1): the explicit space S_loc, comparison with S_0, which conditions are needed | m=4: 6 s, m=7: 16 min |
| `agent_col2_headdiff.py` | task (3): Lambda^tau - Lambda^tau' for one adjacent transposition (m-system and cyclic) | 13 s |
| `agent_col2_positions.py` | task (2): position of a new middle block b; old spans, commutator differences, hull | 17 s |

## Summary

* **Survived (task 1).** S_0 has an explicit, order-free description S_loc by local conditions (sec. 1);
  EXACT-CHECKED S_0 = S_loc for m = 4, 5, 6, 7. The inclusion S_0^tau in S_loc is PROVED for every time order tau
  in which block 0 occurs twice; hence CONJECTURE I (and its extension to non-cyclic positions) follows from
  Q_cyc(m) plus the explicit dimension statement dim S_loc = |fam| - 12, and **Q_cyc(m) <=> the cyclic family
  spans the explicit space S_loc(m)**. At m = 3, S_loc still has the expected dimension but the family spans
  only 105 of 108.
* **Killed.** (2) every position of a new block b gives a step of the same Lambda-twisted type (appending after 0'
  is literally the generic append of the cyclic configuration; middle positions: dense commutator form);
  (3) the head-map change under an adjacent transposition is dense and of full rank, for the m-system and for the
  cyclic family.
* **Next step:** prove dim S_loc = |fam| - 12 (an h^1-vanishing of the same type as the project's L2), then attack
  "the cyclic family spans S_loc" with a residual sequence along the lines of one block (sec. 4).

## 1. Task (1): an explicit, order-free S_0

**Ambient (PROVED).** f in S_0 has poles <= 2 on L_0c and <= 1 on the lines of blocks t >= 1 (AGENT_COL 3.2), so
D_lim f = (X_i g_i)_i with D_lim = D_0^2 prod_{t>=1} D_t, g_i homogeneous of degree d = 3n and sum_i X_i g_i = 0
(each component of a word vector is divisible by X_i). This space V_0 has dimension 3n(3n+2): it is the kernel of
the surjective map S_d^3 -> S_{d+1}, (g_i) -> sum X_i g_i (exactness of the Koszul complex).

**Definition.** S_loc := {g in V_0 satisfying (a), (b), (c1), (c2), (c3)}, with z_cd = L_0c cap L_0d and
z_c = L_0c cap {X_c = 0} the interior and boundary base points of block 0:
* (a) g_i(z) = 0 at the 6 base points of every block t >= 1 (as for W_n);
* (b) g_i in m_z^2 at the 3 interior base points z_cd (fat points);
* (c1) g_i(z_c) = 0 and d/dT g_i(z_c) = 0 for T along {X_c = 0} (length-2 scheme along the coordinate line);
* (c2) d/dL g_i(z_c) = 0 for i != c, L along L_0c;
* (c3) the eps^2-coefficient of (X_i g_i)(z_c + eps Q) (Q on L_0c) is parallel to v_c(z_c) = (A_0(c,i) z_c,i)_i.
None of these refers to the time order.

**EXACT-CHECKED (`agent_col2_sloc.py`, standard order, one point per m):**

| m (n) | dim V_0 | (a) indep. | block-0 conditions | dim S_loc | rank of family numerators | |fam| - 12 |
|---|---|---|---|---|---|---|
| 3 (4) | 168 | 24 | 36 | 108 | **105** | 108 |
| 4 (5) | 255 | 36 | 36 | 183 | 183 | 183 |
| 5 (6) | 360 | 48 | 36 | 276 | 276 | 276 |
| 6 (7) | 483 | 60 | 36 | 387 | 387 | 387 |
| 7 (8) | 624 | 72 | 36 | 516 | 516 | 516 |

Every family member satisfies every condition (m = 3..7). Each group is needed: dropping (a), (b), (c1), (c2),
(c3) raises the dimension by 12(m-1), 18, 9, 3, 3. The flat-limit conditions (a)+(b)+(c1) alone give
|fam| - 6, matching W0(nu1) cap W0(nu2) of AGENT_COL 3.5; (c2) and (c3) are what cut the 6 extra directions.
So S_0 = S_loc for m = 4..7: 6 independent conditions at each of the 6 base points of block 0, versus 2 for W_n,
i.e. 12 more than W_n on the same ambient space.

**Inclusion S_0^tau in S_loc for every order tau (PROVED).** Let tau be any time order of the m blocks with
block 0 occurring twice. (a) Each delta = 0 member is the limit of a member of W_n(delta), whose numerator vanishes at
the fixed base points of blocks t >= 1. (b), (c1) Block N's base points are (1 + delta nu)^{-1} z: an interior one moves
in direction nu∘z, a boundary one z_c moves inside {X_c = 0}. So the limit numerator vanishes on the length-2
schemes; it does not depend on nu, and the directions nu∘z span the tangent space, hence fat points at z_cd.
(c2), (c3) Lemma 1 of AGENT_COL 3.4. It only uses that block 0 occurs at most twice in head + word: dp_c is
(scalar ∝ X_c)(scalar ∝ X_c) v_c (suffix), and the suffix, a product of kernels of blocks >= 1, has zero column c at
X_c = 0. Hence for every order the delta = 0 members of the tau-family lie in S_loc. ∎ Likewise W_m is in S_loc
(PROVED: g = D_0 g_W vanishes to order 2 at all six base points and identically on L_0c).

**Consequences.**
* (PROVED, given CONJECTURE D below) For every order tau whose two copies of block 0 are not adjacent (exactly 12
  members coincide: PROVED by word comparison for cyclic orders, counted for 'last'/'first' in sec. 2):
  S_0^tau = S_loc <=> the distinct delta = 0 tau-members are independent. For cyclic orders this is Q_cyc for a relabelled generic configuration, so at a generic point
  it holds for one cyclic order iff for all. Hence CONJECTURE I follows from Q_cyc(m) and CONJECTURE D.
* **CONJECTURE D:** dim S_loc = |fam| - 12, i.e. the 12(n-2) + 36 conditions are independent on V_0. This is an
  h^1-vanishing for Q(3n-1) twisted by an explicit zero-dimensional scheme, the same type of statement as the
  project's L2 (dim W_n). EXACT-CHECKED m = 3..7. The upper bound follows from Theorem C's local functionals:
  they vanish on S_loc by (b), (c2), (c3) and separate the 12 jets. The lower bound follows from Q_cyc.
* **Reformulation (PROVED, given CONJECTURE D):** Q_cyc(m) <=> the cyclic family spans S_loc(m), an explicit space.
  m = 3 shows that spanning can fail while S_loc has the right dimension.

## 2. Task (2): the position of a new middle block (KILLED)

Old blocks 0..m-2, new block b; positions pos_j (cyclic, b after the j-th old middle block), 'last'
(0, 1..m-2, 0', b) and 'first' (b, 0, 1..m-2, 0').
* **PROVED (word inspection):** the new members (E_b, head b, first letter b) are the same for all positions. b is
  deleted from the word when it is the head or the first letter, and the remaining letters keep their time order. So
  "sum or difference over positions of the new columns" is vacuous; only the old columns Old_j (b inserted into
  their words) depend on the position.
* **EXACT-CHECKED (m = 4, 5):**
  - every position, including the non-cyclic 'last' and 'first', spans the same space S_loc(m), and New is
    independent modulo O_j := span(Old_j) in every case;
  - adjacent positions overlap: dim(O_j cap O_j+1) = 63 (m=4), 90 (m=5);
  - the old spans together fill everything: sum_j O_j = S_loc(m);
  - the commutator differences Ins_j(F) - Ins_j+1(F) = +- h_t W1 [K_c, K_b] W2 have rank 45 / 99, and rank 45 / 93
    modulo O_j (for m = 5 they fill S_loc/O_j).
* **'last' = generic append to the cyclic configuration.** Each old column becomes F K_b + h_t(I - K_b), so
  O_last = Phi_b(S_old) with the cyclic head map. The explicit hull Y_last = S_old K_b + span{h_t(I - K_b)} + E_b
  lies in S_loc(m) and contains O_last, but dim Y_last - dim O_last = 27 (m=4), 39 (m=5) (≈ 9(m-1) + 3). New has
  rank only 48, 54 modulo Y_last, deficient by exactly these numbers. So the step needs the Lambda-twisted
  identification Y_last/O_last, as in the generic append and in T0 of AGENT_COL 4.1.
* **Middle positions, commutator form.** The coordinates of the commutator differences in the basis Old_j u New
  are 100% dense in the New-block (rank 45 / 93). The head sums of their Old-parts are 100% dense with full rank
  9 x (number of old head slots) (36 / 45). Kill criterion met: no position makes the step Lambda-free or
  explicit.

## 3. Task (3): head maps of two orders differing by one adjacent transposition (KILLED)

`agent_col2_headdiff.py`; Delta := Lambda^tau - Lambda^tau' (head-slot sums of the coordinates minus E-spread; for
the cyclic family the two copies of block 0 are separate slots, F_{0,N} in slot 0).
* **PROVED:** columns with head or first letter in {u, v}, and all E's, are common to both families, so Delta
  vanishes on them. The other columns differ by +- h_t W1 [K_u, K_v] W2, and Delta(F^tau) = Lambda^tau'(F^tau' - F^tau).
* **EXACT-CHECKED** (all adjacent middle swaps):
  - m-system: 18 (m=4) and 54 (m=5) differing columns; rank Delta = 18 and 45 = 9m (maximal), 100% dense on
    them, every head slot hit; dim(Head cap (Bod^tau + Bod^tau')) = 18, 45 (the bound is attained);
  - cyclic family: 45 and 99 differing columns; rank Delta = 45 = 9(m+1) and 54 = 9(m+1) (maximal); 100% dense;
    every slot hit.
* No local, low-rank or simple commutator expression: killed.

## 4. Most promising next step

1. Prove CONJECTURE D, dim S_loc = |fam| - 12, as a postulation statement for the explicit scheme (2 conditions at
   each base point of blocks >= 1, 6 at each base point of block 0), by the method of the project's L2. Then
   CONJECTURE I is a theorem modulo Q_cyc, and P(n) <== [the cyclic family spans S_loc(n-1)].
2. Attack this spanning statement with a residual (Horace) sequence along the three lines of one middle block b,
   in the position where residues are simplest. For b right before 0', the residues along L_bc of all old
   columns are (prefix scalar) x v_bc K_0, a rank-one pattern analogous to the longitudinal residues of L4.
   sum_j O_j = S_loc(m) suggests using the insertion positions jointly. Caveat: every single-position step
   tested here carries a dense 9(m-1)-dimensional head-map part. A proof must therefore either carry an
   invariant for the cyclic head map or find a global (non-inductive) argument for spanning S_loc.

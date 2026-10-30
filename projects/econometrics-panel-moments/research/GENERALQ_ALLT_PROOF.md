# The exact number of fixed-effect-free moments, and an explicit basis, for every T (dynamic multinomial logit, Q ≥ 3)

Status (27 Oct 2026, version 3): complete paper proof, checked by the script of sec. 9, independently reviewed
in two rounds (sec. 10).
* Secs. 1–6 (Theorem 1): reviewed in round 1. Repairs made: (Gen) is stated for the labelled family, (4.1) has an
  explicit hypothesis, and the minor points are fixed.
* Sec. 7 (Theorem 2 and Corollaries 3, 4): reviewed in round 2. Repairs made: the proof of Corollary 3 is now
  self-contained, plus the minor points.

This extends Theorem A of research/GENERALQ_PROOF.md from 3 ≤ T ≤ Q + 1 to every T ≥ 3. The proof is
self-contained; secs. 1–3 restate what is needed from GENERALQ_PROOF.md.

## 0. Setting and results

Outcomes y_t ∈ [Q] = {1,…,Q} for t = 1,…,T, initial outcome y_0 fixed. For a fixed effect η ∈ (0,∞)^Q
the model is the Markov chain with transition into period t

    K_t(a, i) = π_t(i, a) η_i / L_{ta}(η),      L_{ta}(η) = Σ_i π_t(i, a) η_i ,

and path probability p_y(η) = Π_{t=1}^T K_t(y_{t−1}, y_t). The **economic domain** (DHW (3)) is
π_t(q, r) = exp(γ_{qr} + x_t'β_q), with covariates x_t (scalar or vector) and (γ, β, x) in a real vector
space; DHW's normalisations are irrelevant below. Write g(q,r) := exp γ_{qr} and u_t(q) := exp(x_t'β_q), so that
π_t(q,r) = g(q,r) u_t(q). (For vector covariates the scalar witness of sec. 2 embeds by setting the other
covariates to zero, so genericity carries over.) The **moment space** is M_T := {m ∈ R^{Q^T} : Σ_y m(y) p_y(η) = 0 for all η > 0}.
DHW (arXiv:2610.17104, eq. (24)) construct ℓ(Q,T) moment functions, counted by their eq. (25):

    ℓ(Q,T) = Σ_{j=0}^{T−3} C(T−1−max(j−(Q−2),0), min(Q−2,j)) · (T−2−j) · Q^{j+1},

and conjecture (Conjecture 1) that for generic parameters they are linearly independent and span M_T.
DHW write that for Q ≥ 3 both halves are open (the upper bound even for T = 3).

**Generic** means: outside a proper analytic subset of the (connected) economic domain, i.e. on an
open dense set whose complement has measure zero.

**Theorem 1 (exact count).** For every Q ≥ 3 and every T ≥ 3, generically on the economic domain and for
every initial outcome, dim M_T = ℓ(Q,T).

**Theorem 2 (explicit basis).** Keep DHW's index set (24)–(25), and replace their pair of generation orders
(t, s_1, r, s_2, T), (t, s_2, r, s_1, T) by (t, s_1, s_2, r, T), (t, s_2, s_1, r, T). The resulting ℓ(Q,T)
moment functions (sec. 7) form a basis of M_T, for every Q ≥ 3 and every T ≥ 3, under the same genericity.

**Corollary 3.** Let Q ≥ 3 and T ≥ 4, consider a block system satisfying (Gen), and suppose DHW's family for
T − 1 periods is a basis for every initial outcome. Then DHW's family for T periods is a basis iff a certain
square matrix of size N_Q(T−2) with constant entries is invertible (sec. 7). It is the matrix of DHW's new
columns in the canonical basis, and it is unitriangular for T ≤ Q + 1.

**Corollary 4.** For 3 ≤ T ≤ Q + 1 and every system satisfying (Gen), DHW's family (24) is a basis of M_T.
(This re-proves Theorem B of GENERALQ_PROOF.md.)

So the number of linearly independent fixed-effect-free moment conditions is exactly DHW's count for every
number of periods. Their construction yields an explicit basis for every (Q,T). What remains of Conjecture 1
for T > Q + 1 (including Q = 3, T ≥ 5) is the invertibility in Corollary 3, for DHW's particular choice of
generation orders. That invertibility does not follow from (Gen): at the witness of Lemma 2.1 it fails for
(Q,T) = (3,5) (sec. 8). For Q = 3, Theorem 1 reproves the project's Lean-checked dimension theorem
dim M_T = 3^T − C(3T,2) + 6(T−1) by a uniform argument.

*Form proved.* Both theorems hold for every positive block system satisfying

(Gen) every subfamily of at most Q members of the indexed family (η_1, …, η_Q; L_{tr} : t ≥ 2, r ∈ [Q]),
with pairwise distinct indices, is linearly independent.

(Gen) is about labelled forms. For example, two blocks s ≠ t ≥ 2 with equal forms violate it; this is the
case x_s = x_t, where dim M_T is larger than ℓ(Q,T), e.g. dim M_4 = 39 for Q = 3. (Gen) is inherited by
subsystems of blocks, and generic economic parameters satisfy it (sec. 2). All inductions are inductions on
this statement. Only the blocks t ≥ 2 enter: block 1 appears only through the cleared factor L_{1,y_0}.

## 1. Polynomial (tensor) form

Let S = R[η_1,…,η_Q], S_d its degree-d part. For t ≥ 2 put

    h_{tr} := η_r Π_{s≠r} L_{ts}   (degree Q),   H_t := span{h_{t1},…,h_{tQ}},   D_t := Π_s L_{ts},

so that **L_{tr} h_{tr} = η_r D_t**. Clearing the denominator L_{1,y_0} Π_{t≥2} D_t,

    p_y(η) = A_y · η_{y_T} · h_{2,y_1} h_{3,y_2} ⋯ h_{T,y_{T−1}} / (L_{1,y_0} Π_{t≥2} D_t),   A_y := Π_t π_t(y_t, y_{t−1}) > 0.

A polynomial vanishing on the positive orthant is zero. So, with
φ_{r_1…r_{T−1}} := Σ_q A_{(r_1,…,r_{T−1},q)} m(r_1,…,r_{T−1},q) η_q ∈ S_1 (a bijection m ↔ φ),

    M_T ≅ { (φ_{r_1…r_{T−1}}) ∈ S_1^{Q^{T−1}} : Σ φ_{r_1…r_{T−1}} h_{2r_1} ⋯ h_{T r_{T−1}} = 0 }.      (1.1)

This is the kernel of the multiplication map S_1 ⊗ H_2 ⊗ ⋯ ⊗ H_T → S_{1+(T−1)Q} written in the spanning
sets h_{tr}. Its image is V_T := S_1 H_2 ⋯ H_T, so dim M_T = Q^T − dim V_T. The kernel does not involve y_0.

## 2. Genericity

Each condition in (Gen) says that certain labelled forms are independent. That holds iff some maximal minor
of their coefficient matrix is nonzero. Fix, for each condition, a minor that is nonzero at the witness below.
Its nonvanishing is a real-analytic condition on the connected economic domain, and it implies the condition.
It holds at the witness, so it holds on an open dense set with null complement. Finitely many such conditions
then hold simultaneously generically. This is all the genericity used.

**Lemma 2.1 (witness).** Put w_r := 2^{r−1} and z_t := 2^{tQ}, and take g(j, r) := w_r^{j−1} and
u_t(j) := z_t^{j−1} for j, r ∈ [Q]. This is an economic point: γ_{jr} = (j−1)(r−1) log 2,
β_j = (j−1) log 2, x_t = tQ. It satisfies (Gen) for any number of blocks.

*Proof.* L_{tr} has coefficient vector (ν^0, ν^1, …, ν^{Q−1}) with node ν = ν_{tr} := z_t w_r = 2^{tQ+r−1};
distinct indices (t,r) give distinct positive nodes. A subfamily {η_i : i ∈ I} ∪ {L_{tr} : (t,r) ∈ P} is
independent iff the |P| × (Q − |I|) matrix (ν_{tr}^{e−1})_{(t,r)∈P, e∉I} has rank |P|. Each |P|-square
submatrix is a generalised Vandermonde matrix: distinct positive nodes, distinct nonnegative exponents. It is
nonsingular, because by Descartes' rule of signs a nonzero real combination Σ_{k=1}^{m} c_k ν^{a_k}
(a_1 < ⋯ < a_m) has at most m − 1 positive zeros (Pólya–Szegő, Problems and Theorems in Analysis II, Part V). ∎

## 3. One block

For a block t, the base locus is B_t := ∪_{s<s'} {L_{ts} = L_{ts'} = 0} ∪ ∪_r {η_r = L_{tr} = 0}, a union of
codimension-2 linear spaces. Every h_{ts} and D_t vanishes on B_t.

**Lemma 3.1.** (i) S_1 ⊗ H_t → S_{Q+1} is injective. (ii) I(B_t)_d = S_{d−Q} H_t for d ≥ Q + 1.
(iii) I(B_t)_Q = H_t ⊕ ⟨D_t⟩.

*Proof* (write L_s, h_s, D). (i) If Σ_r φ_r h_r = 0, reduce modulo the prime L_r: only φ_r h_r survives and
L_r ∤ h_r by (Gen), so φ_r = λ_r L_r with λ_r constant; then D Σ λ_r η_r = 0, so λ = 0.
(iii), (ii): for f ∈ I(B_t)_d, on Π_r := {L_r = 0} the form f vanishes on the Q distinct hyperplanes
{L_s = 0} (s ≠ r) and {η_r = 0} of Π_r (traces of components of B_t; distinct by (Gen)), so
f|_{Π_r} = c_r h_r|_{Π_r} with deg c_r = d − Q (lift c_r to S). Since h_{r'} vanishes on Π_r for r' ≠ r,
f − Σ_r c_r h_r vanishes on every Π_r, so it equals c·D with c ∈ S_{d−Q}. For d = Q this gives (iii)
(directness: restrict a relation to Π_r); for d ≥ Q + 1 use S_1 D ⊆ S_1 H_t (η_s D = L_s h_s). ∎

## 4. Several blocks: the fat ideal, for any number of blocks

Let blocks 1,…,k carry the forms L_{tr} (relabelled), with base loci B_t. Define

    𝔍 = 𝔍^{(k)} := { f ∈ S homogeneous : ord_x f ≥ #{t : x ∈ B_t} for every x ∈ P^{Q−1}(C) }.

Every stratum below is a real linear space, so it is the same to impose the conditions at real points.
A *stratum* is a nonempty projective linear space Z that is an intersection of components of B_t for
distinct t; m_Z := number of blocks involved. For homogeneous f, ord ≥ m_Z on Z means f ∈ I(Z)^{m_Z}
(Z linear), and 𝔍 = ∩_Z I(Z)^{m_Z}, an intersection of I(Z)-primary ideals. Every product Π_t c_t with
c_t ∈ I(B_t) lies in 𝔍. A stratum has at most Q − 1 distinct defining forms (Q of them are independent by
(Gen) and cut out the empty set), and I(Z) is generated by them.

(4.1) *Let L be a linear form such that, for every stratum Z, L together with the defining forms of Z is a
linearly independent set. Then for homogeneous g, L g ∈ 𝔍 implies g ∈ 𝔍.* Indeed L ∉ I(Z), so L is a
nonzerodivisor modulo the I(Z)-primary ideal I(Z)^{m_Z}. (The hypothesis holds for L = L_{t'r} of any block t'
outside the k blocks, when the larger system satisfies (Gen): Z's at most Q − 1 defining forms and L_{t'r} are
at most Q members with distinct indices. Some hypothesis is needed: L_{ta} + L_{tb} vanishes on the stratum
{L_{ta} = L_{tb} = 0}.)

*Flats.* For S ⊆ [k] and r_S = (r_t)_{t∈S} put Λ(S, r_S) := ∩_{t∈S} {L_{t r_t} = 0}, of depth |S|. By (Gen)
it is a nonempty projective linear space of codimension |S| iff |S| ≤ Q − 1, and empty if |S| ≥ Q.
Put m := min(k, Q − 1), the largest depth of a nonempty flat, and

    P(S, r_S) := Π_{t∈S} h_{t r_t} · Π_{u∈[k]∖S} D_u   ∈ 𝔍_{kQ}.

**Lemma 4.1 (capped fat-ideal lemma).** Assume (Gen) and k ≥ 1. The products P(S, r_S) with |S| ≤ m form a
basis of 𝔍_{kQ}, so dim 𝔍_{kQ} = Σ_{j=0}^{m} C(k,j) Q^j. Moreover 𝔍_{kQ+1} = S_1 𝔍_{kQ} = S_1 H_1 ⋯ H_k.

For k ≤ Q − 1 this is Lemma 4.1 of GENERALQ_PROOF.md. The only new point for k ≥ Q is that the descending
induction starts at the largest nonempty depth Q − 1, where flats are points.

*Proof.* Let d ∈ {kQ, kQ+1} and f ∈ 𝔍_d.

(a) *Divisibility on flats of depth ≤ Q − 2.* Let Λ = Λ(S, r_S), |S| ≤ Q − 2. For t ∈ S and s ≠ r_t,
Λ ∩ {L_{ts} = 0} lies in the component {L_{t r_t} = L_{ts} = 0} of B_t, so f vanishes there. If the value r
occurs m_r times among the r_t (t ∈ S), every point of Λ ∩ {η_r = 0} lies in the m_r components
{η_r = L_{tr} = 0} of distinct B_t, so ord ≥ m_r there and (η_r|_Λ)^{m_r} | f|_Λ. By (Gen) (|S| + 2 ≤ Q
forms) the forms L_{ts}|_Λ (t ∈ S, s ≠ r_t) and η_r|_Λ are nonzero and pairwise non-proportional on Λ,
i.e. distinct primes of the coordinate ring of Λ. So Π_{t∈S} h_{t r_t}|_Λ divides f|_Λ.

(b) *The top depth m.* For every flat Λ = Λ(S, r_S) of depth |S| = m choose c̃_{S,r} ∈ S_{d−kQ} with
c̃_{S,r} P(S,r_S) = f on Λ:
  – if m = Q − 1, Λ is a point p and P(S, r_S)(p) ≠ 0. Each factor of P(S, r_S) — η_{r_t} and L_{ts}
    (t ∈ S, s ≠ r_t), and L_{us} (u ∉ S, all s) — together with the Q − 1 forms defining p is a set of Q
    members with distinct indices, hence independent;
  – if m = k ≤ Q − 2, then S = [k], f|_Λ = Π_t h_{t r_t}|_Λ · φ by (a), with deg φ = d − kQ ∈ {0,1};
    take c̃ a lift of φ.
For (S', r') ≠ (S, r) of the same depth m, P(S', r') vanishes on Λ(S, r): if S' = S then r'_t ≠ r_t for
some t and h_{t r'_t} contains L_{t r_t}; if S' ≠ S there is u ∈ S ∖ S' and D_u contains L_{u r_u}.
So f_m := f − Σ_{|S|=m} c̃_{S,r} P(S, r_S) vanishes on every flat of depth m (and there is no nonempty
flat of larger depth).

(c) *Descending depths j = m − 1, …, 1* (so j ≤ Q − 2). Suppose f_{j+1} ∈ 𝔍_d vanishes on every flat of
depth > j. On Λ = Λ(S, r_S), |S| = j, (a) gives f_{j+1}|_Λ = Π_{t∈S} h_{t r_t}|_Λ · φ with
deg φ = d − jQ. For u ∉ S and every s, Λ ∩ {L_{us} = 0} is a flat of depth j + 1 ≤ Q − 1 on which f_{j+1}
vanishes, while the h-product does not vanish identically there (|S| + 2 ≤ Q independent forms). So φ
vanishes on these (k − j)Q hyperplanes of Λ, which are distinct primes by (Gen). Hence
φ = c · Π_{u∉S} D_u|_Λ with deg c = d − kQ. Subtract c̃ P(S, r_S), c̃ a lift of c. Each subtracted term
vanishes on every flat of depth > j (a flat Λ(S', r') with |S'| > j has some u ∈ S' ∖ S, and D_u
contains L_{u r'_u}) and on every other flat of depth j (as in (b)). The remainder f_j vanishes on all
flats of depth ≥ j.

(d) *Depth 0.* f_1 vanishes on every hyperplane {L_{tr} = 0}, so f_1 = c · Π_t D_t with deg c = d − kQ;
subtracting c̃ P(∅) leaves 0.

So f = Σ_{|S|≤m} c̃_{S,r} P(S, r_S) with c̃ ∈ S_{d−kQ}.

*Uniqueness for d = kQ* (constant coefficients). Suppose Σ c_{S,r} P(S, r_S) = 0. Restrict to a flat
Λ(S, r) of depth m. Every P(S', r') with |S'| < |S| vanishes there, because some u ∈ S ∖ S' has D_u
containing L_{u r_u}. Every other P of depth m vanishes there as in (b). P(S, r) itself is not identically
zero there. So c_{S,r} = 0. Descending in the depth in the same way, all coefficients vanish, so the products
are a basis of 𝔍_{kQ}. For d = kQ + 1 the coefficients are linear forms, so 𝔍_{kQ+1} = S_1 𝔍_{kQ}.

Finally S_1 P(S, r_S) ⊆ S_1 Π_t (H_t ⊕ ⟨D_t⟩) = S_1 H_1 ⋯ H_k. To see the equality, replace one factor D_t at a
time: ℓ D_t = Σ_s ℓ_s η_s D_t = Σ_s ℓ_s L_{ts} h_{ts} for ℓ = Σ_s ℓ_s η_s. Conversely
S_1 H_1 ⋯ H_k ⊆ 𝔍_{kQ+1} trivially. ∎

## 5. The quotient space and its canonical basis

Keep k blocks and put D := Π_{t=1}^k D_t and

    K := { g = (g_1,…,g_Q) ∈ (𝔍_{kQ})^Q : Σ_r η_r g_r = 0 }.

Identify g with the rational row vector w(g) := (η_r g_r / D)_{r∈[Q]}; it is zero-sum (Σ_r w_r = 0) and has at
most simple poles along each hyperplane {L_{tr} = 0}, and no other poles. Write μ^u_q := η_q / L_{uq} and
v_{s,q}(η) := (π_s(i,q) η_i)_{i∈[Q]}; note Σ_i v_{s,q}(η)_i = L_{sq}(η).

**Canonical multi-heads.** For H ⊆ [k], s ∈ [k] ∖ H, q_H ∈ [Q]^H, q_0 ∈ [Q]:

    Ĉ(H, q_H; s, q_0) := (Π_{u∈H} μ^u_{q_u}) · η_{q_0} e_{q_0} (I − K_s),

where K_s(a, i) = π_s(i, a) η_i / L_{sa}. Its numerators are (multiply out):
g_i = −π_s(i,q_0) Π_{u∈H} h_{u q_u} · h_{s q_0} · Π_{t∉H∪s} D_t for i ≠ q_0, and
g_{q_0} = Π_{u∈H} h_{u q_u} · (D_s − π_s(q_0,q_0) h_{s q_0}) · Π_{t∉H∪s} D_t.
Each is a product of elements of I(B_t), one per block, of degree kQ; and Σ_i η_i g_i = D · Σ_i w_i = 0
because the rows of K_s sum to 1. So **Ĉ(H, q_H; s, q_0) ∈ K**.

Let 𝒞 := {Ĉ(H, q_H; s, q_0) : |H| ≤ Q − 2}. Its size is N_Q(k) := Σ_{j=0}^{min(Q−2, k−1)} C(k,j)(k−j) Q^{j+1}.

**Iterated residues.** For a nonempty flat Λ = Λ(U, q_U) (1 ≤ |U| ≤ m) and w ∈ K put

    ρ_Λ(w) := ( Π_{u∈U} L_{u q_u} · w )|_Λ ,

a zero-sum rational vector on Λ: after multiplying, the denominator D / Π_{u∈U} L_{u q_u} does not vanish
identically on Λ by (Gen). Then:

(R1) ρ_Λ(Ĉ(H, q_H; s, q_0)) = −(Π_{u∈H} η_{q_u}) η_{q_0} v_{s,q_0}|_Λ if (U, q_U) = (H ∪ {s}, (q_H, q_0)). It is 0
if |U| ≥ |H| + 1 and (U, q_U) is different. In the second case some line L_{u q_u} (u ∈ U) is not among the
|H| + 1 pole lines of Ĉ. It vanishes on Λ, while the remaining product is regular at generic points of Λ.
(For the first case: (L_{s q_0} e_{q_0}(I − K_s))|_{L_{s q_0} = 0} = −v_{s,q_0}.)

Say w has *level ≤ j* if ρ_Λ(w) = 0 for every flat of depth > j.

**Lemma 5.1 (independence).** 𝒞 is linearly independent.

*Proof* (GENERALQ_PROOF.md sec. 6.3, restricted to |H| ≤ Q − 2). Let Σ c(H, q_H; s, q_0) Ĉ(H, q_H; s, q_0) = 0.
Descend on J = |H| from min(Q − 2, k − 1) to 0. Fix U with |U| = J + 1 ≤ Q − 1 and colours q_U, and apply
ρ_Λ, Λ = Λ(U, q_U) (nonempty). Terms with |H| > J have zero coefficient by induction. A term with
|H| ≤ J survives only if its pole lines are exactly the U-lines (R1), i.e. H ∪ {s} = U with the given
colours: J + 1 terms, one per s ∈ U, with images −(Π_{u∈U} η_{q_u}) v_{s,q_s}|_Λ. At a point of Λ where all
η_i ≠ 0 (no η_i lies in the span of the J + 1 defining forms), the vectors v_{s,q_s} = diag(η)(π_s(i,q_s))_i
are independent, because the J + 1 forms L_{s q_s} are. So these coefficients vanish. ∎

**Lemma 5.2 (spanning).** 𝒞 spans K. Hence 𝒞 is a basis of K and dim K = N_Q(k).

*Proof.* Let w ∈ K. It has level ≤ m. We show: if w has level ≤ j with 1 ≤ j ≤ m, there is a
combination w' of members of 𝒞 with |H| = j − 1 such that w − w' has level ≤ j − 1. Then descending
from j = m gives w − (element of span 𝒞) of level 0, and level 0 forces 0:

*Level 0.* Then ρ vanishes on every hyperplane {L_{tr} = 0}, so w has no poles. So D | η_i g_i, hence
D | g_i (η_i is coprime to every L_{tr} by (Gen)). Then g_i = c_i D with c_i constant, by degree. So
w = (c_i η_i)_i with Σ_i c_i η_i = 0, i.e. c = 0.

*The step.* Fix a flat Λ = Λ(U, q_U) with |U| = j. We claim

    ρ_Λ(w) = −Σ_{u∈U} λ_u ρ_Λ(Ĉ(U∖u, q_{U∖u}; u, q_u))   for some constants λ_u.          (5.1)

Granting (5.1), put w' := −Σ_{(U, q_U), |U|=j} Σ_{u∈U} λ^{(U,q)}_u Ĉ(U∖u, q_{U∖u}; u, q_u). By (R1) these
members of 𝒞 (they have |H| = j − 1 ≤ Q − 2) have level ≤ j. Their ρ at the flat (U, q_U) is the
displayed sum, and they have zero ρ at the other flats of depth j. So w − w' has level ≤ j − 1.

*Proof of (5.1) for j = Q − 1.* Then Λ is a point p and ρ_Λ(w) is a zero-sum vector. The Q − 1 vectors
v_{u,q_u}(p) = diag(p)(π_u(i,q_u))_i (u ∈ U) are zero-sum (Σ_i v_{u,q_u}(p)_i = L_{u q_u}(p) = 0). They are
independent because all p_i ≠ 0 (η_i together with the Q − 1 forms defining p is independent) and the Q − 1
coefficient vectors of the forms L_{u q_u} are independent. They therefore span the zero-sum hyperplane, and
Π_{u∈U} η_{q_u}(p) ≠ 0, so (5.1) holds by (R1).

*Proof of (5.1) for j ≤ Q − 2.* Write D' := D / Π_{u∈U} L_{u q_u} = Π_{u∈U} Π_{s≠q_u} L_{us} · Π_{t∉U} D_t, so
ρ_Λ(w)_i = (η_i g_i / D')|_Λ. Exactly as in Lemma 4.1(a), applied to g_i ∈ 𝔍 on the flat Λ (depth j ≤ Q − 2),
g_i|_Λ is divisible by Π_{u∈U} h_{u q_u}|_Λ = Π_{u∈U} η_{q_u} · Π_{u∈U} Π_{s≠q_u} L_{us} |_Λ. Writing
g_i|_Λ = Π_{u∈U} h_{u q_u}|_Λ · φ_i (deg φ_i = (k − j)Q),

    ρ_Λ(w)_i = η_i · Π_{u∈U} η_{q_u} · φ_i / Π_{t∉U} D_t |_Λ .

Since w has level ≤ j, for every t ∉ U and r the flat Λ ∩ {L_{tr} = 0} (depth j + 1 ≤ Q − 1, nonempty)
has ρ = 0. That flat's ρ is the restriction of L_{tr}|_Λ · ρ_Λ(w), so φ_i vanishes on
Λ ∩ {L_{tr} = 0}. These (k − j)Q hyperplanes of Λ are distinct primes by (Gen), so
Π_{t∉U} D_t|_Λ divides φ_i. By degree, φ_i = c_i Π_{t∉U} D_t|_Λ with c_i constant. Therefore

    ρ_Λ(w) = Π_{u∈U} η_{q_u} · (c_i η_i)_i |_Λ ,   c ∈ R^Q.

It is zero-sum, so the linear form c·η vanishes on Λ (Π η_{q_u} ≢ 0 on Λ). The linear forms vanishing on
Λ are spanned by its defining forms, so c·η = Σ_{u∈U} λ_u L_{u q_u}. Comparing coefficient vectors,
c = Σ_u λ_u π_u(·, q_u). Hence (c_i η_i)_i = Σ_u λ_u v_{u,q_u}, and (5.1) follows from (R1). ∎

## 6. Proof of Theorem 1

Let c_T denote dim M_T for a block system with blocks 2..T satisfying (Gen); we show c_T = ℓ(Q,T) for
every T ≥ 2 (with ℓ(Q,2) = 0), by induction on T.

**T = 2:** M_2 = 0 by Lemma 3.1(i) and ℓ(Q,2) = 0 (empty sum).

**Step T → T + 1 (T ≥ 2).** Let φ be a relation (1.1) for blocks 2,…,T+1. Put
ψ_r := Σ φ_{r r_2 … r_T} h_{3 r_2} ⋯ h_{T+1, r_T} ∈ V' := S_1 H_3 ⋯ H_{T+1}; then Σ_r ψ_r h_{2r} = 0.

1. Modulo the prime L_{2r} only ψ_r h_{2r} survives (L_{2r} divides h_{2r'} for r' ≠ r) and L_{2r} ∤ h_{2r}
   (Gen). So ψ_r = L_{2r} g_r, and dividing by D_2 (L_{2r} h_{2r} = η_r D_2): Σ_r η_r g_r = 0.
2. The linear map φ ↦ (g_r) has kernel {ψ_r = 0 for all r} = ⊕_r {relations (1.1) of the T-period system
   with blocks 3,…,T+1}. That system satisfies (Gen), so the kernel has dimension Q c_T.
3. With 𝔍 := 𝔍^{(T−1)} for blocks 3,…,T+1: V' ⊆ 𝔍, and L_{2r} satisfies the hypothesis of (4.1) (it is a
   form of block 2, outside blocks 3,…,T+1). So g_r ∈ 𝔍_{(T−1)Q} by (4.1), and the image lies in K
   (sec. 5, for these T − 1 blocks).
   Conversely, for (g_r) ∈ K put ψ_r := L_{2r} g_r. It lies in 𝔍_{(T−1)Q+1}, which equals V' by Lemma 4.1.
   So ψ_r = Σ φ_{r,·} h_3 ⋯ for some φ_{r,·}, and Σ_r ψ_r h_{2r} = D_2 Σ_r η_r g_r = 0. So the image is all of K.
4. By Lemma 5.2, dim K = N_Q(T−1). Therefore c_{T+1} = Q c_T + N_Q(T−1).

**The count (25) satisfies the same recursion:** ℓ(Q,T+1) = Q ℓ(Q,T) + N_Q(T−1). Split DHW's index
tuples (j, t, s_2, q) for T + 1 periods into two cases.
  – *j ≥ 1 and t_1 = 1.* Dropping period 1 (t' = (t ∖ {1}) − 1, s'_2 = s_2 − 1, q' = (q_0, q_2, …, q_j)) is a
    bijection onto the index tuples for T periods, times the free value q_1 ∈ [Q]. Indeed
    s_1 = 1 + min([T−1] ∖ t'). The restriction "t_r = r for r ≤ j − (Q−2)" for (T+1, j) is equivalent
    to t_1 = 1 together with the restriction for (T, j − 1) on t'. This gives Q ℓ(Q,T) tuples.
  – *otherwise (j = 0, or t_1 ≥ 2).* The restriction forces j ≤ Q − 2. Then t ⊆ {2, …, T} with |t| = j ≤ T − 2,
    s_1 = 1, and s_2 ∈ [T] ∖ (t ∪ {1}) (T − 1 − j choices), q ∈ [Q]^{j+1}. Count:
    Σ_{j=0}^{min(Q−2, T−2)} C(T−1, j)(T−1−j) Q^{j+1} = N_Q(T−1).
Since c_2 = ℓ(Q,2) = 0, c_T = ℓ(Q,T) for all T ≥ 2. Genericity: every condition used is an instance of
(Gen), which holds generically on the economic domain (Lemma 2.1, sec. 2). ∎

*By-products.* dim 𝔍^{(k)}_{kQ} = Σ_{j≤min(k,Q−1)} C(k,j) Q^j and dim 𝔍^{(k)}_{kQ+1} = dim S_1 H_1 ⋯ H_k = Q^{k+1} − ℓ(Q,k+1).

## 7. An explicit basis for every T: the canonical family (Theorem 2)

DHW's family (24) is built from pairs of generation orders (cyclic permutations) that agree on the first
j entries. Their footnote 7 fixes the pair τ_1 = (t, s_1, r, s_2, T), τ_2 = (t, s_2, r, s_1, T), where
r = (r_1 < ⋯ < r_{T−j−3}) are the remaining periods. We keep DHW's index set (24)–(25) exactly, including the
restriction t_r = r for r ≤ j − (Q−2), and change only the pair:

    τ'_1 := (t_1, …, t_j, s_1, s_2, r_1, …, r_{T−j−3}, T),    τ'_2 := (t_1, …, t_j, s_2, s_1, r_1, …, r_{T−j−3}, T),

    m^can_{j,t,s_2,q} := [Π_l 1{y_{t_l} = q_l}] · [ 1{y_{s_1} = q_0} S^{τ'_1} − 1{y_{s_2} = q_0} S^{τ'_2} ],

with S^τ := p^τ / p and p^τ(y) := K_1(y_0, y_{τ(1)}) Π_{k≥2} K_{τ(k−1)+1}(y_{τ(k−1)}, y_{τ(k)}) (DHW (11), (13)).
The new pair still agrees on the first j entries and differs at position j + 1, so this is another instance
of DHW's Theorem 1. For T = 3 the two families coincide.

**Lemma 7.1 (validity).** Each m^can lies in M_T.

*Proof.* τ'_1 and τ'_2 are permutations of [T] ending with T. With τ(0) := 0, the blocks used are
τ(k−1) + 1, k = 1,…,T, i.e. 1,…,T, each once, and block b = τ(k−1) + 1 is entered from y_{τ(k−1)} = y_{b−1},
exactly as in p. So p^τ(y) and p(y) have the same denominators Π_b L_{b, y_{b−1}} and the same η-numerators
Π_t η_{y_t}. Hence S^τ = Π_k π_{τ(k−1)+1}(y_{τ(k)}, y_{τ(k−1)}) / Π_b π_b(y_b, y_{b−1}) does not depend on η.
Next, Σ_y m^can(y) p_y(η) = P^{τ'_1}(y_t = q, y_{s_1} = q_0) − P^{τ'_2}(y_t = q, y_{s_2} = q_0). Under p^τ the
coordinates are generated one by one, in the order τ, by stochastic kernels. Both orders first generate
y_{t_1}, …, y_{t_j} by K_1(y_0, ·), K_{t_1+1}, …, K_{t_{j−1}+1}, and then the (j+1)-th coordinate (y_{s_1},
respectively y_{s_2}) from y_{t_j} by the same kernel K_{t_j+1} (K_1(y_0, ·) if j = 0). So both probabilities
equal c(q) := K_1(y_0, q_1) Π_{l<j} K_{t_l+1}(q_l, q_{l+1}) K_{t_j+1}(q_j, q_0), with c(q) := K_1(y_0, q_0) if
j = 0. ∎

**Lemma 7.2 (lifts and quotient images).**
(a) If j ≥ 1 and t_1 = 1, then m^can = 1{y_1 = q_1} m', where m' is the canonical moment of the (T−1)-period
chain on periods 2,…,T started at y_1 = q_1, for the shifted tuple (j − 1, t' = (t ∖ {1}) − 1,
s'_2 = s_2 − 1, q' = (q_0, q_2, …, q_j)). By the bijection of sec. 6 these lifts are exactly Q disjoint copies
(q_1 ∈ [Q]) of the canonical (T−1)-period family.
(b) Otherwise (s_1 = 1 and j ≤ Q − 2), the quotient map ρ(m)_i := Σ_{y : y_1 = i} m(y) p_y(η) gives

    ρ(m^can) = c(q) · e_{q_0} (I − K_{s_2+1}) .                                              (7.1)

*Proof.* (a) Both orders start with period 1, so p^{τ'} = K_1(y_0, y_1) p'^{τ''} and p = K_1(y_0, y_1) p', where
τ'' is the order of the shorter chain. τ'' is the canonical order of the shifted tuple: s'_1 = s_1 − 1 is the
minimum of the remaining periods, and the r's shift to r − 1. The restriction rule shifts as in sec. 6.
(b) In the τ'_1-term, the fixed outcomes are generated, then y_1 = q_0 (forcing i = q_0), then the free
outcomes; summing out the free outcomes leaves δ_{i q_0} c(q). In the τ'_2-term, the fixed outcomes and
y_{s_2} = q_0 are generated. Next y_1 = i is generated from y_{s_2} by block s_2 + 1, and the free outcomes
are summed out. This leaves c(q) K_{s_2+1}(q_0, i). ∎

In the block notation of secs. 5–6 (sec. 6, steps 1 and 3, with T in place of T + 1), take a moment m of the
T-period system and let g be the element of K, for the k = T − 2 blocks 3,…,T, that sec. 6 attaches to m. Then

    ρ(m) = w(g) / L_{1,y_0},

since ρ(m)_r = h_{2r} ψ_r / (L_{1,y_0} Π_{t≥2} D_t) and ψ_r = L_{2r} g_r. Since
c(q) = κ · η_{q_1} ⋯ η_{q_j} η_{q_0} / (L_{1,y_0} Π_l L_{t_l+1, q_l}) with κ a nonzero product of π's,
(7.1) reads

    ρ(m^can) = (κ / L_{1,y_0}) · Ĉ(H, q_H; s, q_0),    H := {t_l + 1}, q_{t_l+1} := q_l, s := s_2 + 1.

As (t, s_2, q) runs over the non-lift tuples (j = 0 or t_1 ≥ 2, hence j ≤ Q − 2), (H, q_H, s, q_0) runs
bijectively over the index set of 𝒞 for the blocks 3,…,T (H ⊆ {3,…,T}, |H| ≤ Q − 2, s ∉ H). Equivalently, the
element g ∈ K attached to m^can is κ times the numerator vector of Ĉ(H, q_H; s, q_0).

*Proof of Theorem 2.* Induction on T, for all (Gen) systems and all initial outcomes. ρ is linear, and its
kernel is the space of lifts ⊕_{q_1} 1{y_1 = q_1} M_{T−1}(start q_1) (sec. 6, step 2). Its image lies in
{w(g)/L_{1,y_0} : g ∈ K} (sec. 6, step 3, which uses only (4.1)). By Lemma 5.2 the image therefore has dimension
at most |𝒞| = N_Q(T−2). By Lemma 7.2(b), the elements g attached to the non-lift canonical moments are
κ times the numerator vectors of the distinct members of 𝒞. By Lemma 5.1 they are independent, so the
non-lift canonical images form a basis of the image of ρ, which is therefore all of
{w(g)/L_{1,y_0} : g ∈ K}.
For T = 3 there are no lift members (j ≤ T − 3 = 0) and the kernel of ρ is ⊕ M_2 = 0 (Lemma 3.1(i)), so the
Q canonical moments form a basis of M_3. For T ≥ 4, by induction the canonical (T−1)-families are bases of the
M_{T−1}(start q_1), and by Lemma 7.2(a) their lifts are the lift members. Hence the canonical family is a basis
of M_T, and dim M_T = Q ℓ(Q, T−1) + N_Q(T−2) = ℓ(Q,T) (sec. 6).
This is a second proof of Theorem 1. It avoids the conclusion of Lemma 4.1 (the lifting step of sec. 6). But
Lemma 5.2 still uses the divisibility step (a) from that proof. ∎

*Proof of Corollary 3.* First, the three facts about DHW's family that the argument needs.

(i) *Lifts.* When j ≥ 1 and t_1 = 1, DHW's orders τ_1 = (t, s_1, r, s_2, T), τ_2 = (t, s_2, r, s_1, T) both start
with period 1. Shifting periods by one gives DHW's orders for the shifted tuple: s'_1 = s_1 − 1, s'_2 = s_2 − 1,
and r' = r − 1, still increasing. As in Lemma 7.2(a), m^DHW = 1{y_1 = q_1} m'^DHW, and by the bijection of
sec. 6 the lift members are Q disjoint copies of DHW's (T−1)-family. ρ kills them.

(ii) *Images.* For a non-lift tuple, as in Lemma 7.2(b),

    ρ(m^DHW) = c(q) · e_{q_0} (I − K_{s_2+1} K_{r_1+1} ⋯ K_{r_n+1}),   n := T − j − 3.

The τ_1-term gives δ_{i q_0} c(q). In the τ_2-term, y_{s_2} = q_0 is followed by y_{r_1}, …, y_{r_n} and then y_1,
generated by the blocks s_2 + 1, r_1 + 1, …, r_n + 1 in turn.

(iii) *Expansion.* With A_0 := K_{s_2+1} and A_m := K_{r_m+1}:
I − A_0 A_1 ⋯ A_n = Σ_{m=0}^{n} A_0 ⋯ A_{m−1} (I − A_m). Using
η_a e_a K_b = Σ_{a'} π_b(a', a) μ^b_a η_{a'} e_{a'} repeatedly, each term becomes
η_{q_0} e_{q_0} A_0 ⋯ A_{m−1}(I − A_m) = Σ_{a_1,…,a_m} [Π_{i<m} π_{b_i}(a_{i+1}, a_i) μ^{b_i}_{a_i}] E_{b_m, a_m},
where b_0 := s_2 + 1, b_i := r_i + 1 and a_0 := q_0. Multiplied by the head factors Π_{u∈H} μ^u_{q_u}, this is a
combination with constant coefficients of the canonical multi-heads
Ĉ(H ∪ {b_0, …, b_{m−1}}; b_m, a_m), whose heads have size j + m ≤ T − 3. The term m = 0 is Ĉ(H, q_H; s, q_0)
itself, with coefficient 1.

*The corollary.* By (i), ρ kills the lift members, which are Q disjoint copies of DHW's (T−1)-family. These are
bases by hypothesis, so DHW's family is a basis iff the images of its non-lift members span the image of ρ,
i.e. iff their elements g ∈ K are a basis of K. By (ii), (iii) and the computation of c(q) after Lemma 7.2,
each such g is κ(q) times a combination of numerator vectors of multi-heads with constant coefficients, and κ(q)
is the same constant as for the canonical moment with the same tuple. In the basis of canonical images (the
κ(q)-multiples of 𝒞, Lemma 5.2), the matrix is therefore square of size N_Q(T−2), with constant entries.
Order rows and columns by |H|. Every multi-head in (iii) has a head set strictly larger than H, except the
term m = 0.
– For T ≤ Q + 1, all of them have heads of size ≤ T − 3 ≤ Q − 2, so they lie in 𝒞, and the matrix is
  unitriangular.
– For T > Q + 1, the multi-heads with |H| ≥ Q − 1 must first be re-expressed in 𝒞 by the procedure in the proof
  of Lemma 5.2. ∎

*Proof of Corollary 4.* For T = 3 the canonical and DHW families coincide (Theorem 2). For 4 ≤ T ≤ Q + 1 use
induction and Corollary 3: the matrix is unitriangular, hence invertible. ∎

*Remark (Q = 3).* For Q = 3 the matrix of Corollary 3 is R_n, n = T − 2, of HQ_FRESH_APPROACH.md. Up to
constants, 𝒞 = {E_{s,a}} ∪ {B_{t,s,a,b}} there.

## 8. Remarks

* **Q = 3.** Strata are the 6k base points (m_Z = 1), so 𝔍 = I(Z) and Lemma 4.1 reads
  dim I(Z)_{3k} = 1 + 3k + 9C(k,2) and I(Z)_{3k+1} = S_1 H_1 ⋯ H_k. This is the core of the project's Lean
  theorem. K is the space W_k of HQ_FRESH_APPROACH.md, and Lemma 5.2 is the project's L2, now with a direct
  proof. The non-lift canonical moments have images E_{s,a} (j = 0) and B_{t,s,a,b} (j = 1), up to constants.
* **Scope of (Gen).** (Gen) is sufficient, not necessary: some violations leave the dimensions unchanged
  (e.g. L_{21} through the vertex {L_{11} = L_{12} = 0}, Q = 3).
  – (Gen) needs distinct time-varying covariates for the blocks t ≥ 2. With x_s = x_t (s ≠ t ≥ 2), two blocks
    have equal labelled forms and the dimension is larger, e.g. Q = 3: dim M_3 = 9 and dim M_4 = 39 instead of 3
    and 33. A tie with block 1 is harmless; with x_1 = x_2, the referee found dim M_T = ℓ at
    (3,3), (3,4), (3,5), (4,4).
  – Coinciding slopes β_q also break (Gen); e.g. {η_3, L_{21}, L_{31}} becomes dependent, and dim M_5 = 168
    for Q = 3.
  – DHW's parsimonious empirical specification (4), z_t(q, y_{t−1}) = γ_q 1{y_{t−1} = q} + X_{t,q} β, has
    L_{tr} − L_{ts} ∈ span(η_r, η_s). So it violates (Gen) identically for Q ≥ 4, and the theorems say
    nothing there; the referee found dim M_T = ℓ numerically for (Q,T) = (4,4), (4,5). For Q = 3 we have not
    proved (Gen) on (4); the referee found dim M_T = ℓ there for T ≤ 6.
  – The economic domain of the theorems is DHW's general specification (3).
* **(Gen) does not suffice for DHW's own family when T > Q + 1.** The witness of Lemma 2.1 satisfies (Gen),
  and all its forms are tangent lines of one conic. There, the referee found (exact over Q):
  – DHW's (3,5) family has rank 159 < 162, and the matrix of Corollary 3 has rank 60 < 63;
  – at (3,6), DHW's family has rank 597 < 606, a deficit inherited through the lifts, while the matrix of
    Corollary 3 has full rank 120;
  – the canonical family has full rank at these points, as Theorem 2 says.
  The same deficit appears at every point π_t(j, r) = (z_t w_r)^{j−1} tried. (The project's earlier
  "Vandermonde common conic, three-block residue rank 51/54" is the same phenomenon.) So a proof of
  Conjecture 1 for T > Q + 1 needs genericity beyond (Gen), and a witness off this locus. At generic economic
  points DHW's family is a basis for all (Q,T) tested.

## 9. Machine checks

`exploration/hq_fresh_generalQ_allT.py` (math/.venv; exact arithmetic mod p = 2^61 − 1, exact rationals where
stated) checks:
* the canonical family: the exact quotient images (7.1) of every non-lift member at (Q,T) = (3,5), (4,5);
  raw rank ℓ(Q,T) with every row a valid moment at (3,5), (3,6), (4,6); DHW's family at (3,5), (3,6);
* (Gen) at the witness;
* Lemma 4.1: the products P(S, r_S) lie in 𝔍, are independent and span 𝔍_{kQ}, and
  S_1 𝔍_{kQ} = 𝔍_{kQ+1} = S_1 H_1 ⋯ H_k;
* Lemma 5.2: 𝒞 ⊆ K, rank N_Q(k), and dim K = N_Q(k), at the witness and at a random point, for
  (Q,k) = (3,2..5), (4,3..5), including k ≥ Q;
* raw dim M_T = ℓ(Q,T) from path likelihoods for (Q,T) = (3,5), (3,6), (4,6);
* the recursion ℓ(Q,T+1) = Q ℓ(Q,T) + N_Q(T−1) against (25) and DHW's Table 1.

All checks pass. They are checks at points, not part of the proof.

## 10. Review

**First review (secs. 0–6 and 8 of version 1; fresh referee given only this document and DHW's paper;
27 Oct 2026).** Verdict: the document proves Theorem 1 after minor repairs; no mathematical gap.

The referee checked every step by hand:
* Lemma 4.1 for k ≥ Q;
* Lemma 5.2 (numerators, (R1) with sign, the restriction identity for ρ, divisibility, the steps j = Q − 1 and
  level 0, and the cases k = 1, Q − 1, Q, Q = 3);
* every use of (Gen) (none needs more than Q forms);
* the fibration;
* the recursion against (25), including DHW's restriction.

The referee's own exact checks (mod 2^61 − 1; witness runs mod the prime 2305844108725321739, because 2 has
order 61 modulo 2^61 − 1):
* raw dim M_T = ℓ(Q,T) for Q = 3, T = 3..9, for Q = 4, T = 3..6, and for Q = 5, T = 3..5, at economic, general
  and witness points;
* the fat ideal from its definition for Q = 3, k = 1..8, and for Q = 4, k = 1..5: dim 𝔍_{kQ}, dim 𝔍_{kQ+1} and
  dim K all as stated;
* (Gen) at the witness exactly over Z, up to 174436 subsets;
* stress tests: configurations with extra incidences that still satisfy (Gen) give the generic dimensions.
  Some violations of (Gen) move the dimensions, others do not;
* all 56 Table 1 entries.

Findings and their repair in this version:
1. (Gen), read as "sets of distinct forms", is satisfied by two identical blocks, where the conclusion fails.
   Repaired: (Gen) is stated for the labelled family with distinct indices; this is the version every step
   uses, and the witness satisfies it.
2. (4.1) is false for an arbitrary L distinct from the defining forms (e.g. L_{ta} + L_{tb}). Repaired: it now
   assumes that L together with each stratum's defining forms is independent; this holds for L = L_{2r}, the
   only use.
3. Minor points, repaired:
   – the index range in Lemma 4.1(b);
   – the explicit vanishing of lower-depth products in the uniqueness step;
   – "j ≥ 1 and t_1 = 1" in the split of sec. 6;
   – Lemma 2.1: definitions, notation and a citation;
   – the wording in sec. 2 and the field in sec. 4;
   – the inductive form of the statement in Corollary 3;
   – the scope remark of sec. 8.

**Second review (sec. 7 of version 2, Theorem 2 and Corollary 3; same referee, same rules; 27 Oct 2026).**
Verdict: Theorem 2 is correctly proved; Corollary 3 is true, but its proof cited GENERALQ_PROOF.md for three
facts.

The referee checked by hand:
* Lemma 7.1, both parts;
* Lemma 7.2(a) and (b), noting that the canonical pair puts y_1 at position j + 2, right after y_{s_2};
* the identification ρ(m) = w(g)/L_{1,y_0} (because h_{2r} ψ_r = η_r D_2 g_r);
* c(q), the bijection onto the index set of 𝒞, and the induction.

The referee's own exact checks (mod 2^61 − 1, at economic points; general points agree):

| (Q,T) | ℓ | rank canonical / DHW | Corollary 3 matrix |
|---|---|---|---|
| (3,4) | 33 | 33 / 33 | unitriangular |
| (4,4) | 56 | 56 / 56 | unitriangular |
| (4,5) | 524 | 524 / 524 | unitriangular |
| (5,4) | 85 | 85 / 85 | unitriangular |
| (5,5) | 965 | 965 / 965 | unitriangular |
| (3,5) | 162 | 162 / 162 | full rank, not triangular |
| (3,6) | 606 | 606 / 606 | full rank |
| (3,7) | 2013 | 2013 / 2013 | full rank |
| (4,6) | 3072 | 3072 / 3072 | full rank |

Also:
* every row of both families is a valid moment;
* (7.1), Lemma 7.2(a) and the DHW image formula hold for every member, and exactly over Q as polynomial
  identities at (3,4), (4,4), (3,5);
* the matrix of Corollary 3 has constant entries;
* swapping in the canonical pair changes the family for every T ≥ 4, but not its span (generically);
* the witness finding recorded in sec. 8.

Findings and their repair in this version (all follow the referee's own derivations, which it verified):
1. Corollary 3's proof was not self-contained. Repaired: facts (i) lifts, (ii) the DHW image formula and
   (iii) the expansion are now proved in place.
2. The Q = 3 clause (R_n) was part of Corollary 3's statement without proof here. Moved to a remark.
3. Minor points, all repaired:
   – the T = 3 base case now cites M_2 = 0;
   – it is now said that the second proof of Theorem 1 still uses step (a) of Lemma 4.1's proof;
   – the multiplier κ/L_{1,y_0} is no longer called a constant;
   – "unitriangular" now refers to the basis of canonical images;
   – block labels r_i + 1, and "j ≥ 1 and t_1 = 1";
   – (Gen) is added to Corollary 3, and Corollary 4 (T ≤ Q + 1) is stated;
   – scalar vs. vector covariates; s ≠ t ≥ 2 in the x_s = x_t example;
   – coinciding β_q; the softened claim about specification (4) for Q = 3;
   – the witness caution;
   – two misreports of the first round in this section (the witness prime, and the effect of (Gen)
     violations).

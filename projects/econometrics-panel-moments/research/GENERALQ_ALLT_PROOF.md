# The exact number of fixed-effect-free moments for every T (dynamic multinomial logit, Q ≥ 3)

Status (27 Oct 2026): complete paper proof, checked by the script of sec. 8. Independent review: sec. 9.
This extends Theorem A of research/GENERALQ_PROOF.md from 3 ≤ T ≤ Q + 1 to every T ≥ 3. The proof is
self-contained; secs. 1–3 restate what is needed from GENERALQ_PROOF.md.

## 0. Setting and result

Outcomes y_t ∈ [Q] = {1,…,Q} for t = 1,…,T, initial outcome y_0 fixed. For a fixed effect η ∈ (0,∞)^Q
the model is the Markov chain with transition into period t

    K_t(a, i) = π_t(i, a) η_i / L_{ta}(η),      L_{ta}(η) = Σ_i π_t(i, a) η_i ,

and path probability p_y(η) = Π_{t=1}^T K_t(y_{t−1}, y_t). The **economic domain** is
π_t(q, r) = exp(γ_{qr} + x_t β_q) with (γ, β, x) in a real vector space (DHW's normalisations are
irrelevant below). The **moment space** is M_T := {m ∈ R^{Q^T} : Σ_y m(y) p_y(η) = 0 for all η > 0}.
DHW (arXiv:2610.17104, eq. (24)) construct ℓ(Q,T) moment functions, counted by their eq. (25):

    ℓ(Q,T) = Σ_{j=0}^{T−3} C(T−1−max(j−(Q−2),0), min(Q−2,j)) · (T−2−j) · Q^{j+1},

and conjecture (Conjecture 1) that for generic parameters they are linearly independent and span M_T.
DHW write that for Q ≥ 3 both halves are open (the upper bound even for T = 3).

**Generic** means: outside a proper analytic subset of the (connected) economic domain, i.e. on an
open dense set whose complement has measure zero.

**Theorem.** For every Q ≥ 3 and every T ≥ 3, generically on the economic domain and for every initial
outcome, dim M_T = ℓ(Q,T).

So the number of linearly independent fixed-effect-free moment conditions is exactly DHW's count, for
every number of periods. Consequently, for each (Q,T), DHW's Conjecture 1 is equivalent to the linear
independence of the family (24) alone (which is proved for T ≤ Q + 1 in GENERALQ_PROOF.md, Theorem B;
it is open for T > Q + 1, including Q = 3, T ≥ 5). For Q = 3 the theorem reproves the project's
Lean-checked dimension theorem dim M_T = 3^T − C(3T,2) + 6(T−1) by a different, uniform argument.

*Form proved.* The theorem holds for every positive block system satisfying

(Gen) every set of at most Q distinct linear forms from {η_1,…,η_Q} ∪ {L_{tr}} is linearly independent,

which is inherited by subsystems of blocks; generic economic parameters satisfy (Gen) (sec. 2). All
inductions are inductions on this statement.

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

Every condition used below has the form "a set of at most Q distinct forms from {η_i} ∪ {L_{tr}} is
linearly independent", i.e. the nonvanishing of a minor, an analytic function on the connected economic
domain. It therefore holds generically once it holds at one economic point.

**Lemma 2.1 (witness).** g(j,r) = w_r^{j−1}, u_t(j) = z_t^{j−1} with w_r = 2^{r−1}, z_t = 2^{tQ} (an economic
point: γ_{jr} = (j−1)(r−1) log 2, β_j = (j−1) log 2, x_t = tQ) satisfies every such condition, for any
number of blocks. *Proof.* L_{tr} has coefficient vector (x^0,…,x^{Q−1}) with node x = 2^{tQ+r−1};
distinct (t,r) give distinct positive nodes. A set {η_i : i ∈ I} ∪ {L_{tr} : (t,r) ∈ P} is independent
iff the |P| × (Q − |I|) matrix (x_k^{e−1})_{k∈P, e∉I} has rank |P|. Its |P|-square minors are generalised
Vandermonde determinants with distinct positive nodes and distinct exponents, hence nonzero. ∎

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

    𝔍 = 𝔍^{(k)} := { f ∈ S homogeneous : ord_x f ≥ #{t : x ∈ B_t} for every x ∈ P^{Q−1} }.

A *stratum* is a nonempty projective linear space Z that is an intersection of components of B_t for
distinct t; m_Z := number of blocks involved. For homogeneous f, ord ≥ m_Z on Z means f ∈ I(Z)^{m_Z}
(Z linear), and 𝔍 = ∩_Z I(Z)^{m_Z}, an intersection of I(Z)-primary ideals. Every product Π_t c_t with
c_t ∈ I(B_t) lies in 𝔍. A stratum has at most Q − 1 distinct defining forms (Q distinct forms are
independent by (Gen) and cut out the empty set). Hence:

(4.1) *If a linear form L is distinct from all defining forms of all strata, then for homogeneous g,
L g ∈ 𝔍 implies g ∈ 𝔍* (by (Gen), L ∉ I(Z), so L is a nonzerodivisor modulo the I(Z)-primary I(Z)^{m_Z}).

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
  – if m = Q − 1, Λ is a point p and P(S, r_S)(p) ≠ 0, because each factor η_{r_t}, L_{ts} (t ∈ S),
    L_{us} (u ∉ S) together with the Q − 1 forms defining p is a set of Q independent forms;
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

So f = Σ_{|S|≤m} c̃_{S,r} P(S, r_S) with c̃ ∈ S_{d−kQ}. For d = kQ the coefficients are constants, and
they are determined by f: applying (b)–(d) to f = 0 forces every coefficient to vanish (at each depth the
restriction to Λ(S, r) sees only the term P(S, r), whose restriction is not identically zero). So the
products are a basis of 𝔍_{kQ}. For d = kQ + 1 the coefficients are linear forms, so 𝔍_{kQ+1} = S_1 𝔍_{kQ}.
Finally S_1 P(S, r_S) ⊆ S_1 Π_t (H_t ⊕ ⟨D_t⟩) = S_1 H_1 ⋯ H_k, using η_s D_t = L_{ts} h_{ts}; and
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

## 6. Proof of the theorem

Let c_T denote dim M_T for a block system with blocks 2..T satisfying (Gen); we show c_T = ℓ(Q,T) for
every T ≥ 2 (with ℓ(Q,2) = 0), by induction on T.

**T = 2:** M_2 = 0 by Lemma 3.1(i) and ℓ(Q,2) = 0 (empty sum).

**Step T → T + 1 (T ≥ 2).** Let φ be a relation (1.1) for blocks 2,…,T+1. Put
ψ_r := Σ φ_{r r_2 … r_T} h_{3 r_2} ⋯ h_{T+1, r_T} ∈ V' := S_1 H_3 ⋯ H_{T+1}; then Σ_r ψ_r h_{2r} = 0.

1. Modulo the prime L_{2r} only ψ_r h_{2r} survives (L_{2r} divides h_{2r'} for r' ≠ r) and L_{2r} ∤ h_{2r}
   (Gen). So ψ_r = L_{2r} g_r, and dividing by D_2 (L_{2r} h_{2r} = η_r D_2): Σ_r η_r g_r = 0.
2. The linear map φ ↦ (g_r) has kernel {ψ_r = 0 for all r} = ⊕_r {relations (1.1) of the T-period system
   with blocks 3,…,T+1}. That system satisfies (Gen), so the kernel has dimension Q c_T.
3. With 𝔍 := 𝔍^{(T−1)} for blocks 3,…,T+1: V' ⊆ 𝔍 and L_{2r} is distinct from all defining forms of the
   strata, so g_r ∈ 𝔍_{(T−1)Q} by (4.1). Hence the image lies in K (sec. 5, for these T − 1 blocks).
   Conversely, for (g_r) ∈ K put ψ_r := L_{2r} g_r. It lies in 𝔍_{(T−1)Q+1}, which equals V' by Lemma 4.1.
   So ψ_r = Σ φ_{r,·} h_3 ⋯ for some φ_{r,·}, and Σ_r ψ_r h_{2r} = D_2 Σ_r η_r g_r = 0. So the image is all of K.
4. By Lemma 5.2, dim K = N_Q(T−1). Therefore c_{T+1} = Q c_T + N_Q(T−1).

**The count (25) satisfies the same recursion:** ℓ(Q,T+1) = Q ℓ(Q,T) + N_Q(T−1). Split DHW's index
tuples (j, t, s_2, q) for T + 1 periods by whether t_1 = 1.
  – *t_1 = 1.* Dropping period 1 (t' = (t ∖ {1}) − 1, s'_2 = s_2 − 1, q' = (q_0, q_2, …, q_j)) is a
    bijection onto the index tuples for T periods, times the free value q_1 ∈ [Q]. Indeed
    s_1 = 1 + min([T−1] ∖ t'). The restriction "t_r = r for r ≤ j − (Q−2)" for (T+1, j) is equivalent
    to t_1 = 1 together with the restriction for (T, j − 1) on t'. This gives Q ℓ(Q,T) tuples.
  – *t_1 ≠ 1.* The restriction forces j ≤ Q − 2. Then t ⊆ {2, …, T} with |t| = j ≤ T − 2, s_1 = 1, and
    s_2 ∈ [T] ∖ (t ∪ {1}) (T − 1 − j choices), q ∈ [Q]^{j+1}. Count:
    Σ_{j=0}^{min(Q−2, T−2)} C(T−1, j)(T−1−j) Q^{j+1} = N_Q(T−1).
Since c_2 = ℓ(Q,2) = 0, c_T = ℓ(Q,T) for all T ≥ 2. Genericity: every condition used is an instance of
(Gen), which holds generically on the economic domain (Lemma 2.1, sec. 2). ∎

*By-products.* dim 𝔍^{(k)}_{kQ} = Σ_{j≤min(k,Q−1)} C(k,j) Q^j and dim 𝔍^{(k)}_{kQ+1} = dim S_1 H_1 ⋯ H_k = Q^{k+1} − ℓ(Q,k+1).

## 7. Remarks

* **Q = 3.** Strata are the 6k base points (m_Z = 1), so 𝔍 = I(Z) and Lemma 4.1 reads
  dim I(Z)_{3k} = 1 + 3k + 9C(k,2) and I(Z)_{3k+1} = S_1 H_1 ⋯ H_k: the project's Lean theorem. K is the space W_k
  of HQ_FRESH_APPROACH.md, and 𝒞 = {E_{s,a}} ∪ {canonical B_{t,s,a,b}} (up to constants): Lemma 5.2 is the
  project's L2, now with a direct proof.
* **What remains of Conjecture 1 for T > Q + 1.** The new (non-lift) images of DHW's columns are
  N(H, q_H; s, q_0) = (Π_{u∈H} μ^u_{q_u}) J^R_{s,q_0} with |H| ≤ Q − 2 (GENERALQ_PROOF.md (6.1)). They expand
  unitriangularly over all canonical multi-heads (GENERALQ_PROOF.md sec. 6.2), but the multi-heads with
  |H| ≥ Q − 1 are not in 𝒞. The procedure in the proof of Lemma 5.2 re-expresses them in 𝒞; their
  coefficients are values of the μ's at points of flats of depth Q − 1. Conjecture 1 for (Q,T) is
  equivalent to the invertibility of the resulting square matrix, of size N_Q(T−2); for Q = 3 this is det R_n ≠ 0.

## 8. Machine checks

`exploration/hq_fresh_generalQ_allT.py` (math/.venv; exact arithmetic mod p = 2^61 − 1 at the stated
points) checks: (Gen) at the witness; Lemma 4.1 (the products P(S, r_S) lie in 𝔍, are independent, and
span 𝔍_{kQ}, and S_1 𝔍_{kQ} = 𝔍_{kQ+1} = S_1 H_1 ⋯ H_k); Lemma 5.2 (𝒞 ⊆ K, rank N_Q(k),
dim K = N_Q(k)) for (Q,k) with k ≥ Q among them; raw dim M_T = ℓ(Q,T) from path likelihoods for
(Q,T) = (3,5), (3,6), (4,6) (all with T > Q + 1); and the recursion ℓ(Q,T+1) = Q ℓ(Q,T) + N_Q(T−1)
against (25) and DHW's Table 1. These are checks at points, not part of the proof.

## 9. Review

(pending)

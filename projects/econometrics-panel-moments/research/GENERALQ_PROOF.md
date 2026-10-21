# DHW Conjecture 1 for every T ≤ Q+1 (exact moment counts and bases) in dynamic multinomial logit

Status (21 Oct 2026): complete paper proof, checked by the scripts listed in sec. 7; independently
reviewed (sec. 8), with the reviewer's gap and minor points repaired in this version.

## 0. Setting and results

Outcomes y_t ∈ [Q] = {1,…,Q} for t = 1,…,T, initial outcome y_0 fixed. For a fixed effect
η ∈ (0,∞)^Q (η_q = exp α_q) the model is the Markov chain with transition into period t

    K_t(a, i) = π_t(i, a) η_i / L_{ta}(η),      L_{ta}(η) = Σ_i π_t(i, a) η_i ,

so the path probability is p_y(η) = Π_{t=1}^T K_t(y_{t−1}, y_t). The **economic domain** is
π_t(q, r) = exp(γ_{qr} + x_t β_q), with (γ, β, x) ranging over a real vector space (with
DHW's normalisations γ_{1r} = γ_{q1} = β_1 = 0; nothing below depends on them). Write
g(i, a) := exp γ_{ia}, u_t(i) := exp(x_t β_i), so π_t(i, a) = g(i, a) u_t(i): every block is a
torus translate of one matrix ("product form").

The **moment space** is M_T := {m ∈ R^{Q^T} : Σ_y m(y) p_y(η) = 0 for all η > 0}.
DHW (arXiv:2610.17104, eq. (24)) give ℓ(Q, T) explicit elements of M_T (eq. (25) counts them)
and conjecture (Conjecture 1) that they form a basis for generic parameters. DHW prove their
independence for T = 3; both halves are open for Q ≥ 3, T ≥ 4 (and the upper bound for T = 3).

Throughout, **generic** means: outside a proper analytic subset of the (connected) economic domain, i.e. on
an open dense set whose complement has measure zero (this covers DHW's "outside a null set"; the witness
below embeds in models with several regressors by taking the other covariates zero).

Both theorems are stated for Q ≥ 3; for Q = 2 the range T ≤ Q + 1 is T = 3, which is classical.

**Theorem A (exact count).** For Q ≥ 3 and 3 ≤ T ≤ Q + 1, generically
dim M_T = ℓ(Q, T) = Q^T − Q (2 + Q − T)(1 + Q)^{T−2}.

**Theorem B (bases).** For Q ≥ 3 and 3 ≤ T ≤ Q + 1, generically the DHW family
(24) is linearly independent, hence (Theorem A) a basis of M_T. So both halves of Conjecture 1 hold
whenever T ≤ Q + 1; in particular at T = 3 and T = 4 for every Q ≥ 3.

*Form proved.* Both theorems hold for every positive block system satisfying
(Gen): every set of at most Q distinct linear forms from {η_1,…,η_Q} ∪ {L_{tr}} is linearly independent.
(Gen) is inherited by subsystems of blocks, and generic economic parameters satisfy it (sec. 2); the
inductions below are inductions on this statement.

## 1. Polynomial (tensor) form

Let S = R[η_1,…,η_Q] with S_d its degree-d part. For t ≥ 2 put

    h_{tr} := η_r Π_{s ≠ r} L_{ts}  (degree Q),   H_t := span{h_{t1},…,h_{tQ}},   D_t := Π_s L_{ts}.

Note the identity  **L_{tr} h_{tr} = η_r D_t.**

Clearing the common denominator D := L_{1,y_0} Π_{t ≥ 2} D_t,

    p_y(η) = A_y · η_{y_T} · h_{2, y_1} h_{3, y_2} ⋯ h_{T, y_{T−1}} / D,
    A_y := Π_t π_t(y_t, y_{t−1}) > 0.

(Indeed η_{y_T} Π_{t≥2} h_{t, y_{t−1}} = Π_{t=1}^T η_{y_t} · Π_{t≥2} Π_{r ≠ y_{t−1}} L_{tr}.) A
polynomial vanishing on the positive orthant is zero, so with φ_{r_1…r_{T−1}} :=
Σ_{q} A_{(r_1,…,r_{T−1},q)} m(r_1,…,r_{T−1},q) η_q ∈ S_1 (a bijection m ↔ φ, since A_y ≠ 0):

    M_T ≅ { (φ_{r_1…r_{T−1}}) ∈ S_1^{Q^{T−1}} :  Σ φ_{r_1…r_{T−1}} h_{2 r_1} ⋯ h_{T r_{T−1}} = 0 },   (1.1)

the kernel of the multiplication map μ_T : S_1 ⊗ H_2 ⊗ ⋯ ⊗ H_T → S_{1+(T−1)Q} (written in the
spanning sets h_{tr}). We write V_T := image of μ_T = S_1 H_2 ⋯ H_T, so dim M_T = Q^T − dim V_T.

## 2. Genericity: one witness for every condition

All conditions used below have the form: **a set F of at most Q distinct linear forms, taken
from {η_1,…,η_Q} ∪ {L_{tr}}, is linearly independent.** Each is the nonvanishing of a minor of the
coefficient matrix, a polynomial in (g, u). Composed with the exponential parametrisation it is
real-analytic on the connected economic domain, so it holds on an open dense set as soon as it
holds at one economic point; finitely many such conditions then hold simultaneously on an open
dense set.

**Lemma 2.1 (witness).** Take g(j, r) = w_r^{j−1}, u_t(j) = z_t^{j−1} (j, r ∈ [Q]) with w_r = 2^{r−1},
z_t = 2^{tQ}. This is an economic point (γ_{jr} = (j−1)(r−1) log 2, β_j = (j−1) log 2, x_t = tQ),
and every condition of the above form holds there.

*Proof.* The coefficient vector of L_{tr} is (x^{0}, x^{1}, …, x^{Q−1}) with node x = z_t w_r = 2^{tQ + r − 1};
distinct pairs (t, r) have distinct positive nodes. Let F consist of η_i (i ∈ I) and |P| forms L_{tr}.
Modulo the η_i, independence means that the |P| × (Q − |I|) matrix (x_k^{e})_{k ∈ P, e ∉ I} (exponents
e − 1 over the coordinates outside I) has rank |P| ≤ Q − |I|. Each |P|-square submatrix is a
generalised Vandermonde matrix with distinct positive nodes and distinct exponents, whose
determinant is nonzero (such matrices are strictly totally positive). ∎

(The same witness, z = 2, is the project's Lean-checked economic witness for Q = 3.)

## 3. One block

Fix a block t (write L_s, h_s, H, D) with base locus

    B := ∪_{s<s'} {L_s = L_{s'} = 0}  ∪  ∪_r {η_r = L_r = 0}     (linear spaces of codimension 2).

Every h_s and D vanishes on B. Genericity used: (G) for each r, the Q forms L_s (s ≠ r) and η_r are
pairwise non-proportional and nonzero on Π_r := {L_r = 0} (independence of {L_r, ℓ, ℓ'}).

**Lemma 3.1.**
(i) S_1 ⊗ H → S_{Q+1} is injective (and h_1,…,h_Q are independent).
(ii) I(B)_k = S_{k−Q} H for every k ≥ Q + 1.
(iii) I(B)_Q = H ⊕ ⟨D⟩.

*Proof.* (i) If Σ_r φ_r h_r = 0, reduce modulo the prime L_r: only φ_r h_r survives and L_r ∤ h_r by (G),
so φ_r = λ_r L_r with λ_r constant; then D Σ λ_r η_r = 0, so λ = 0.
(iii) Let f ∈ I(B)_Q. On Π_r, f vanishes on the Q distinct hyperplanes {L_s = 0} (s ≠ r) and {η_r = 0}
of Π_r (they are the traces of components of B), hence f|_{Π_r} = c_r h_r|_{Π_r} by degree. Since
h_{r'} vanishes on Π_r for r' ≠ r, f − Σ c_r h_r vanishes on every Π_r, so it is d·D. Directness:
restrict a relation to Π_r.
(ii) The same restriction gives f|_{Π_r} = c_r h_r|_{Π_r} with c_r of degree k − Q (lift it to S), and
f − Σ c_r h_r = c D with c ∈ S_{k−Q}. Finally S_1 D ⊆ S_1 H because η_s D = L_s h_s. ∎

## 4. Several blocks: the fat ideal

Let blocks t = 1,…,k carry lines L_{tr}, with base loci B_t. Define

    𝔍^{(k)} := { f ∈ S homogeneous : ord_x f ≥ #{t : x ∈ B_t} for every point x ∈ P^{Q−1} }.

Every product Π_t c_t with c_t ∈ I(B_t) lies in 𝔍^{(k)}. Call a *stratum* every NONEMPTY projective
linear space Z obtained as an intersection of components of distinct B_t, and m_Z the number of blocks
involved. For homogeneous f, ord_x f ≥ m_Z on Z is the condition f ∈ I(Z)^{(m_Z)} = I(Z)^{m_Z} (Z linear),
and 𝔍^{(k)} = ∩_Z I(Z)^{m_Z}; these are I(Z)-primary. Under (Gen) a stratum has at most Q − 1 distinct
defining forms (Q distinct forms are independent and cut out the empty set), so for a form L distinct from
them, L ∉ I(Z) is an independence condition of at most Q forms. Hence

(4.1) *if a linear form L is distinct from all defining forms of all strata (so L vanishes identically on no
stratum by (Gen)), then for homogeneous g, L g ∈ 𝔍^{(k)} implies g ∈ 𝔍^{(k)}.*

(Points are projective throughout: intersections of components that are empty in P^{Q−1} impose nothing.)

For S ⊆ [k] and r_S = (r_t)_{t ∈ S} put Λ(S, r_S) := ∩_{t ∈ S} {L_{t r_t} = 0}, the *flat* of depth |S|
(not to be confused with the strata above).

**Lemma 4.1 (fat-ideal lemma).** Let 1 ≤ k ≤ Q − 1 and assume (Gen). Then

    𝔍^{(k)}_{kQ} = Π_{t=1}^k (H_t ⊕ ⟨D_t⟩),  of dimension (Q+1)^k,   and
    𝔍^{(k)}_{kQ+1} = S_1 · Π_t (H_t ⊕ ⟨D_t⟩) = S_1 H_1 ⋯ H_k.

*Proof.* Let d ∈ {kQ, kQ+1} and f ∈ 𝔍^{(k)}_d. Since k ≤ Q − 1, every flat Λ(S, r_S) is a nonempty
projective linear space of codimension |S| (projective dimension Q − 1 − |S| ≥ 0).

*Divisibility on flats.* On Λ := Λ(S, r_S), f|_Λ is divisible by Π_{t ∈ S} h_{t r_t}|_Λ. Indeed, for
t ∈ S and s ≠ r_t, Λ ∩ {L_{ts} = 0} lies in the component {L_{t r_t} = L_{ts} = 0} of B_t, so f|_Λ vanishes
there. If the value r occurs m_r times among the r_t (t ∈ S), every point of Λ ∩ {η_r = 0} lies in the
m_r components {η_r = L_{tr} = 0}, so the fat condition gives ord ≥ m_r there, i.e. (η_r|_Λ)^{m_r} | f|_Λ.
If Λ has positive dimension, (Gen) makes the forms L_{ts}|_Λ (t ∈ S, s ≠ r_t) and η_r|_Λ pairwise
non-proportional and nonzero on Λ (independence of |S| + 2 ≤ Q forms), so their product with the stated
multiplicities, which is Π_{t ∈ S} h_{t r_t}|_Λ, divides f|_Λ. If Λ is a single point (|S| = Q − 1), the
restricted h-product is a nonzero number (independence of Q forms) and divisibility is automatic.

*Descending induction on the depth.* Put f_k := f.
(a) |S| = k: on Λ([k], r), f|_Λ = c_r Π_t h_{t r_t}|_Λ with deg c_r = d − kQ ∈ {0, 1}. Subtract
Σ_r c̃_r Π_t h_{t r_t} (c̃_r any lift of c_r). On Λ([k], r') every product with r ≠ r' vanishes (it contains
L_{t r'_t} for some t), so the remainder f_{k−1} vanishes on every flat of depth k.
(b) Suppose f_j vanishes on all flats of depth > j (1 ≤ j < k). On Λ = Λ(S, r_S) with |S| = j,
f_j|_Λ = Π_{t ∈ S} h_{t r_t}|_Λ · φ, deg φ = (k − j)Q + (d − kQ). For u ∉ S and every s, Λ ∩ {L_{us} = 0} is a
flat of depth j + 1 on which f_j vanishes, while the h-product does not vanish identically there (|S| + 2
independent forms); so φ vanishes on these (k − j)Q distinct hyperplanes of Λ (distinct by (Gen)) and
φ = c · Π_{u ∉ S} D_u|_Λ with deg c = d − kQ. Subtract Σ_{S, r_S} c̃ Π_{t∈S} h_{t r_t} Π_{u∉S} D_u. Each subtracted
term vanishes on every flat of depth > j (it contains a D_u with u ∉ S, which vanishes on {L_{u r'_u} = 0}) and
on every other flat of depth j (it contains L_{t r'_t} through h_{t r_t} with r_t ≠ r'_t, or a D_u with u ∈ S'),
so the remainder f_{j−1} vanishes on all flats of depth ≥ j.
(c) (depth 0) f_0 vanishes on every hyperplane {L_{tr} = 0}, so f_0 = c · Π_t D_t with deg c = d − kQ; subtracting
c̃ Π_t D_t leaves 0.

Hence f is a combination of the products Π_{t∈S} h_{t r_t} Π_{u∉S} D_u with coefficients in S_{d−kQ}. For
d = kQ the coefficients are constants and are determined by f (by (a)–(c) applied to f = 0), so the
(Q+1)^k products are independent. For d = kQ + 1 we get S_1 · Π(H_t ⊕ ⟨D_t⟩), and S_1 D_t ⊆ S_1 H_t
(η_s D_t = L_{ts} h_{ts}) absorbs every D_t: S_1 Π(H_t ⊕ ⟨D_t⟩) = S_1 Π H_t. Conversely all these
products lie in 𝔍^{(k)}. ∎

## 5. Proof of Theorem A

Induction on T for all block systems satisfying (Gen), starting at **T = 2**: M_2 = 0 by Lemma 3.1 (i).
**Step T → T + 1 for 2 ≤ T ≤ Q.** Let φ be a relation (1.1) for blocks 2,…,T+1 and put
ψ_r := Σ φ_{r r_3 … r_{T+1}} h_{3 r_3} ⋯ h_{T+1, r_{T+1}} ∈ V' := S_1 H_3 ⋯ H_{T+1}.

1. Σ_r ψ_r h_{2r} = 0. Modulo the prime L_{2r} only ψ_r h_{2r} survives and L_{2r} ∤ h_{2r} (genericity),
   so ψ_r = L_{2r} g_r, and dividing by D_2: Σ_r η_r g_r = 0.
2. The linear map φ ↦ (g_r) has kernel ⊕_r {relations among the factors 3,…,T+1}, i.e. Q copies of the
   T-period moment space of the system with blocks 3,…,T+1 (in the roles of 2,…,T), which satisfies (Gen);
   by induction its dimension is Q c_T.
3. With k = T − 1 ∈ [1, Q − 1] blocks 3,…,T+1 and J := 𝔍^{(T−1)}: V' ⊆ J, and L_{2r} is distinct from all
   defining forms of the strata, so by (4.1) g_r ∈ J_{(T−1)Q}. Conversely, by Lemma 4.1,
   L_{2r} J_{(T−1)Q} ⊆ J_{(T−1)Q+1} = V', so every (g_r) ∈ J_{(T−1)Q}^Q with Σ η_r g_r = 0 comes from a
   relation (ψ_r := L_{2r} g_r ∈ V', choose φ with these ψ_r; then Σ ψ_r h_{2r} = D_2 Σ η_r g_r = 0).
   Hence the image is K := {(g_r) ∈ J_{(T−1)Q}^Q : Σ η_r g_r = 0}, of dimension
   Q dim J_{(T−1)Q} − dim(S_1 J_{(T−1)Q}) = Q (Q+1)^{T−1} − dim V' = Q (Q+1)^{T−1} − (Q^T − c_T),
   using S_1 J_{(T−1)Q} = J_{(T−1)Q+1} = V' (Lemma 4.1) and dim V' = Q^T − (T-period moment dimension).
4. Therefore dim M_{T+1} = (Q+1) c_T + Q (Q+1)^{T−1} − Q^T.

(For k = 1, Lemma 4.1 is Lemma 3.1 (ii), (iii).) The closed form c_T := Q^T − Q(2+Q−T)(1+Q)^{T−2}
has c_2 = 0 and satisfies c_{T+1} = (Q+1) c_T + Q (Q+1)^{T−1} − Q^T (expand: the right side is
Q^{T+1} − Q(Q+1)^{T−1}[(2+Q−T) − 1]), so dim M_T = c_T for 2 ≤ T ≤ Q + 1. In particular dim M_3 = Q.

*c_T = ℓ(Q, T) for Q ≥ T − 1.* Then every j ≤ T − 3 ≤ Q − 2 in (25), so with m = T − 1,
ℓ = Σ_{j=0}^{m−2} C(m, j)(m − 1 − j) Q^{j+1}. Using Σ_j C(m,j) Q^j = (1+Q)^m,
Σ_j j C(m,j) Q^j = mQ(1+Q)^{m−1}, and the values 0 (j = m−1) and −Q^m (j = m) of the summand,
ℓ = Q[(m−1)(1+Q)^m − mQ(1+Q)^{m−1} + Q^m] = Q^T − Q(2+Q−T)(1+Q)^{T−2}. ∎

All genericity conditions used are instances of (Gen) (for Q ≥ 3), so sec. 2 applies.

## 6. Proof of Theorem B (independence for 3 ≤ T ≤ Q + 1)

Periods are one-based; K_t is the transition into period t. Write μ^u_c := η_c / L_{uc} (a scalar
rational function), E_{s,c} := η_c e_c (I − K_s), and for a set R of blocks and s ∈ R
J^R_{s,c} := η_c e_c (I − K_s Π_{R∖s}) with Π_{R∖s} the increasing (time-ordered) product.

### 6.1 The family, the lifts and the quotient map

DHW (24) indexes moments by j ∈ [0, T−3], shared periods t_1 < ⋯ < t_j in [T−1], s_1 := min([T−1] ∖ t),
s_2 ∈ [T−1] ∖ (t ∪ {s_1}), values q = (q_0, …, q_j); the generation orders are
τ_1 = (t, s_1, r, s_2, T) and τ_2 = (t, s_2, r, s_1, T) (r the remaining periods, increasing), and the restriction
t_l = l for l ≤ j − (Q−2) is vacuous because j ≤ T − 3 ≤ Q − 2. With p^σ the transformed model (DHW (11), (13)),
p^σ(y) = K_1(y_0, y_{τ(1)}) Π_{k ≥ 2} K_{τ(k−1)+1}(y_{τ(k−1)}, y_{τ(k)}), and
m · p = 1{y_{t_l} = q_l ∀l} [1{y_{s_1} = q_0} p^{σ_1} − 1{y_{s_2} = q_0} p^{σ_2}].

*Lifts* (t_1 = 1). Then s_1 ≥ 2, the restriction rule shifts consistently, and m = 1{y_1 = q_1} m' with m' the
(24)-moment of the (T−1)-period chain on periods 2,…,T started at y_1 = q_1 (blocks K_2,…,K_T): indeed
p^σ = K_1(y_0, y_1) p'^{σ'} and p = K_1(y_0,y_1) p'. So the lifts are Q copies (q_1 ∈ [Q]) of the (T−1)-family
with disjoint supports; by induction on T (the statement is for every initial outcome) they are independent.

*Quotient map.* ρ(m)_i := Σ_{y : y_1 = i} m(y) p_y(η). For a lift, ρ(m) = δ_{i q_1} K_1(y_0,q_1) E[m' | y_1 = q_1] = 0.

*New columns* (t_1 ≥ 2, so s_1 = 1). Summing the stochastic factors after the last fixed outcome: the τ_1-term
generates y_{t_1}, …, y_{t_j} (fixed), then y_1 = q_0 (fixed, forced = i), then free outcomes, giving
δ_{i q_0} c(q), c(q) := K_1(y_0,q_1) Π_{l<j} K_{t_l+1}(q_l, q_{l+1}) K_{t_j+1}(q_j, q_0);
the τ_2-term generates the same fixed outcomes, then y_{s_2} = q_0, then the periods r, then y_1 = i, giving
c(q) (K_{s_2+1} Π_{l} K_{r_l+1})(q_0, i). Hence

    ρ(m) = c(q) e_{q_0} (I − K_{s_2+1} Π_l K_{r_l + 1}).                        (6.1)

(For j = 0: c = K_1(y_0, q_0).) Since K_u(a,b) = π_u(b,a) η_b / L_{ua}, c(q) = κ · (η_{q_1}⋯η_{q_j} η_{q_0}) /
(L_{1 y_0} Π_l L_{t_l+1, q_l}) with κ ≠ 0 a product of π's. So, up to the common factor 1/L_{1,y_0} and κ,

    ρ(m) = N(H, q_H; s, q_0) := (Π_{u ∈ H} μ^u_{q_u}) J^{R}_{s, q_0},

with blocks numbered by their period u ∈ {3,…,T} (n := T − 2 blocks), H := {t_l + 1} (head blocks), q_u := q_l
for u = t_l + 1, R := {3,…,T} ∖ H, s := s_2 + 1 ∈ R. As (t, s_2, q) ranges over the new indices, (H, q_H, s, q_0)
ranges over ALL tuples with H ⊆ {3,…,T}, |H| ≤ n − 1, s ∈ R, q_H ∈ [Q]^H, q_0 ∈ [Q] (bijectively).

### 6.2 Unitriangularity over canonical multi-heads

Define the canonical columns Ĉ(H, q_H; s, q_0) := (Π_{u ∈ H} μ^u_{q_u}) E_{s, q_0}, on the same index set.
From η_c e_c K_u = Σ_d π_u(d,c) μ^u_c η_d e_d we get, for R ∋ s with next block r_1 = min(R ∖ s),
J^R_{s,q_0} = E_{s,q_0} + Σ_d π_s(d,q_0) μ^s_{q_0} J^{R∖s}_{r_1, d}, and iterating,

    N(H, q_H; s, q_0) = Ĉ(H, q_H; s, q_0) + Σ (constants) · Ĉ(H', q'_{H'}; s', q'_0),   |H'| > |H|.

So the matrix of the N's in terms of the Ĉ's is unitriangular for any order by decreasing |H|.

### 6.3 The canonical columns are independent when n ≤ Q − 1

Let a relation Σ c(H, q_H; s, q_0) Ĉ(H, q_H; s, q_0) = 0 hold. Descending induction on k = |H|, from n − 1 to 0.
Fix U, a set of k + 1 blocks, and states (q_u)_{u ∈ U}; let Λ := ∩_{u ∈ U} {L_{u q_u} = 0}, of codimension
k + 1 ≤ n ≤ Q − 1 (nonempty, sec. 2). Multiply the relation by Π_{u ∈ U} L_{u q_u} and restrict to Λ. A column
Ĉ(H', q'; s', q'_0) has denominators only among the |H'| + 1 lines L_{u q'_u} (u ∈ H') and L_{s' q'_0}, one per block
of H' ∪ {s'} (the e_{q'_0} part of E has no pole at all). Columns with |H'| > k vanish by induction. If a column
with |H'| ≤ k has a U-line that is not among its denominators, the uncancelled factor makes it vanish on Λ; so
only columns whose denominators are exactly the U-lines can survive, i.e. H' ∪ {s'} = U with the given states.
For those, every denominator is cancelled and no other line occurs; (for the record: a line L_{va} not among
the U-lines vanishes identically on no such Λ, by independence of k + 2 ≤ Q forms). These are k + 1 columns,
one for each s' ∈ U, and

    (Π_{u ∈ U} L_{u q_u}) Ĉ(U ∖ s', q; s', q_{s'}) |_Λ = − (Π_{u ∈ U} η_{q_u}) v_{s', q_{s'}},  v_{ua}(η) := (π_u(i,a) η_i)_i.

At a point of Λ with all η_i ≠ 0 (exists: no η_i is in the span of the defining forms) the k + 1 vectors
v_{s', q_{s'}} = diag(η) (π_{s'}(i, q_{s'}))_i are independent, since the k + 1 ≤ Q − 1 forms L_{s' q_{s'}} are
(sec. 2). So all coefficients with H ∪ {s} = U vanish; U and the states were arbitrary. ∎

### 6.4 Assembly

A relation among all ℓ(Q,T) moments maps under ρ to a relation among the N's (lifts are killed); by 6.2 and 6.3
(n = T − 2 ≤ Q − 1) all new coefficients vanish; the remaining relation among the lifts is trivial by induction
(applied to the (T−1)-period chains started at q_1, which satisfy (Gen)).
For T = 3 there are no lifts and the new columns are the E_{3,q} (n = 1). Hence the (24) family is independent;
with Theorem A it is a basis. ∎

*Remark (why T > Q + 1 is different).* For n ≥ Q the strata of codimension n are empty and the canonical
multi-heads with |H| ≥ Q − 1 are dependent on the others (e.g. Q = 3, n = 3: rank 63 of 144); DHW's restriction
then removes the new columns with j > Q − 2, and the expansion of 6.2 produces higher-head terms that must be
re-expressed in a smaller basis. For Q = 3, T ≥ 5 this is the open problem (the dense determinant R_n).

## 7. Machine checks (exploration/, run with math/.venv/bin/python)

* `hq_fresh_generalQ_T3.py`: Lemma 3.1 (i)-(iii) for Q = 3..6 and dim M_3 = Q from raw likelihoods.
* `hq_fresh_generalQ_T4.py`: the two-block case of Lemma 4.1, dim S_1H_3H_4 = Q^3 − Q, raw dim M_4 = 3Q^2 + 2Q.
* `hq_fresh_generalQ_dim.py`: Lemma 4.1 for (Q,k) = (3,1),(3,2),(4,2),(4,3),(5,2),(5,3) (fat conditions by
  all partial derivatives at random points of every stratum, witness point) and raw dim M_T = ℓ(Q,T) for
  (Q,T) up to (5,5), with distinct covariates.
* `hq_fresh_generalQ_multihead.py`: formula (6.1) for every new column at (Q,T) = (3,4),(4,4),(4,5),(5,5)
  (exact rational brute-force path sums), and full rank of the canonical multi-heads for
  (Q,n) = (3,2),(4,2),(4,3),(5,3),(5,4) (rank deficient at (3,3), as the remark predicts).
* `hq_fresh_generalQ.py`: full rank of the raw (24) family at economic points.

All checks are exact modular (2^61 − 1) or exact rational arithmetic at the stated points; they test the
lemmas at particular points and are not part of the proof.

## 8. Review

An independent referee (fresh agent, given only this document and DHW's paper, 21 Oct 2026) checked every
section by hand, recomputed formula (6.1) in three cases (T = 5, t = (2,3), s_2 = 4; T = 6, t = (2,4), s_2 = 3;
T = 6, t = (2,3), s_2 = 5), and re-checked numerically (exact, mod 2^61 − 1, own scripts): raw dim M_T = ℓ(Q,T)
for (Q,T) = (2,3), (3,3), (3,4), (4,4), (4,5), (5,4), (5,5), and Lemma 4.1 together with what sec. 5 needs from it
for (Q,k) = (2,1), (3,1), (3,2), (4,1), (4,2), (4,3), (5,2), (5,3). Verdict: the document proves Theorems A and B
once one gap is repaired. Findings and their repair in this version:
1. GAP: "L_{2r} vanishes on no stratum" was false for intersections that are only the origin. Repaired by working
   with projective points (strata are nonempty projective spaces; 𝔍 and (4.1) restated in sec. 4).
2. Q = 2: condition (G) needs three forms. Repaired by stating the theorems for Q ≥ 3 (Q = 2 is classical).
3. Lemma 4.1 (b)/(c) overlap at depth 0. Repaired: (b) for 1 ≤ j < k, (c) is the depth-0 step.
4. "When Λ is a point": clarified (single projective point, |S| = Q − 1; non-proportionality only used in
   positive dimension).
5. Overloaded names: strata vs flats; quotient map now ρ, canonical columns Ĉ, fat ideal 𝔍.
6. The inductions are on the (Gen) version of the statements (sec. 0), which subsystems inherit.
7. Sec. 6.3: the survival argument now states the uncancelled-factor mechanism and the k + 2 ≤ Q condition.
8. Meaning of generic: proper analytic exceptional set (open dense, measure zero).

# Exact moment counts for T ≤ Q+1, and bases for T ≤ 4, in dynamic multinomial logit

Status (20 Oct 2026): complete paper proof, checked by the scripts listed in sec. 7.
Independent review: see sec. 8.

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

Throughout, **generic** means: on an open dense subset of the economic domain.

**Theorem A (exact count).** For Q ≥ 2 and 3 ≤ T ≤ Q + 1, generically
dim M_T = ℓ(Q, T) = Q^T − Q (2 + Q − T)(1 + Q)^{T−2}.

**Theorem B (bases).** Generically, the DHW family (24) is a basis of M_3 (every Q ≥ 2) and of
M_4 (every Q ≥ 3). In particular Conjecture 1 holds at T = 3 and T = 4 for every Q.

(Q = 2 is classical; the proofs below are written for Q ≥ 3 but Theorem A's argument also covers
Q = 2.)

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

    J^{(k)} := { f ∈ S : ord_x f ≥ #{t : x ∈ B_t} for every point x }.

Every product Π_t c_t with c_t ∈ I(B_t) lies in J^{(k)}. J^{(k)} is the intersection of the powers
I(Z)^{m_Z} over the *strata* Z (intersections of components of distinct B_t, all linear spaces), and
powers of ideals generated by independent linear forms are primary; hence

(4.1) *if a linear form L vanishes identically on no stratum, then L g ∈ J^{(k)} implies g ∈ J^{(k)}.*

For S ⊆ [k] and r_S = (r_t)_{t ∈ S} put Λ(S, r_S) := ∩_{t ∈ S} {L_{t r_t} = 0}.

**Lemma 4.1 (fat-ideal lemma).** Let 1 ≤ k ≤ Q − 1 and assume genericity (sec. 2). Then

    J^{(k)}_{kQ} = Π_{t=1}^k (H_t ⊕ ⟨D_t⟩),  of dimension (Q+1)^k,   and
    J^{(k)}_{kQ+1} = S_1 · Π_t (H_t ⊕ ⟨D_t⟩) = S_1 H_1 ⋯ H_k.

*Proof.* Let d ∈ {kQ, kQ+1} and f ∈ J^{(k)}_d. Since k ≤ Q − 1, every Λ(S, r_S) is a linear space of
codimension |S|, nonempty.

*Divisibility on strata.* On Λ := Λ(S, r_S), f|_Λ is divisible by Π_{t ∈ S} h_{t r_t}|_Λ. Indeed, for
t ∈ S and s ≠ r_t, Λ ∩ {L_{ts} = 0} lies in the component {L_{t r_t} = L_{ts} = 0} of B_t, so f|_Λ vanishes
there. If the value r occurs m_r times among the r_t (t ∈ S), every point of Λ ∩ {η_r = 0} lies in the
m_r components {η_r = L_{tr} = 0}, so the fat condition gives ord ≥ m_r there, i.e. (η_r|_Λ)^{m_r} | f|_Λ.
By genericity the forms L_{ts}|_Λ (t ∈ S, s ≠ r_t) and η_r|_Λ are pairwise non-proportional nonzero
forms on Λ (when Λ is a point this step is vacuous), so their product with the stated multiplicities,
which is Π_{t ∈ S} h_{t r_t}|_Λ, divides f|_Λ.

*Descending induction on |S|.* Put f_k := f.
(a) |S| = k: on Λ([k], r), f|_Λ = c_r Π_t h_{t r_t}|_Λ with deg c_r = d − kQ ∈ {0, 1}. Subtract
Σ_r c̃_r Π_t h_{t r_t} (c̃_r any lift of c_r). On Λ([k], r') every product with r ≠ r' vanishes (it contains
L_{t r'_t} for some t), so the remainder f_{k−1} vanishes on every stratum of depth k.
(b) Suppose f_j vanishes on all strata of depth > j (0 ≤ j < k). On Λ = Λ(S, r_S) with |S| = j,
f_j|_Λ = Π_{t ∈ S} h_{t r_t}|_Λ · φ, deg φ = (k − j)Q + (d − kQ). For u ∉ S and every s, Λ ∩ {L_{us} = 0} is a
stratum of depth j + 1 on which f_j vanishes, while the h-product does not vanish identically there;
so φ vanishes on these (k − j)Q distinct hyperplanes of Λ and φ = c · Π_{u ∉ S} D_u|_Λ with deg c = d − kQ.
Subtract Σ_{S, r_S} c̃ Π_{t∈S} h_{t r_t} Π_{u∉S} D_u. Each subtracted term vanishes on every stratum of depth
> j (it contains a D_u with u ∉ S, which vanishes on {L_{u r'_u} = 0}) and on every other stratum of depth j
(it contains L_{t r'_t} through h_{t r_t} with r_t ≠ r'_t, or a D_u with u ∈ S'), so the remainder f_{j−1}
vanishes on all strata of depth ≥ j.
(c) f_{−1} vanishes on every hyperplane {L_{tr} = 0}, so it is c · Π_t D_t with deg c = d − kQ.

Hence f is a combination of the products Π_{t∈S} h_{t r_t} Π_{u∉S} D_u with coefficients in S_{d−kQ}. For
d = kQ the coefficients are constants and are determined by f (by (a)–(c) applied to f = 0), so the
(Q+1)^k products are independent. For d = kQ + 1 we get S_1 · Π(H_t ⊕ ⟨D_t⟩), and S_1 D_t ⊆ S_1 H_t
(η_s D_t = L_{ts} h_{ts}) absorbs every D_t: S_1 Π(H_t ⊕ ⟨D_t⟩) = S_1 Π H_t. Conversely all these
products lie in J^{(k)}. ∎

## 5. Proof of Theorem A

Induction on T, starting at **T = 2**: M_2 = 0 by Lemma 3.1 (i) (relations of S_1 ⊗ H_2).
**Step T → T + 1 for 2 ≤ T ≤ Q.** Let φ be a relation (1.1) for blocks 2,…,T+1 and put
ψ_r := Σ φ_{r r_3 … r_{T+1}} h_{3 r_3} ⋯ h_{T+1, r_{T+1}} ∈ V' := S_1 H_3 ⋯ H_{T+1}.

1. Σ_r ψ_r h_{2r} = 0. Modulo the prime L_{2r} only ψ_r h_{2r} survives and L_{2r} ∤ h_{2r} (genericity),
   so ψ_r = L_{2r} g_r, and dividing by D_2: Σ_r η_r g_r = 0.
2. The linear map φ ↦ (g_r) has kernel ⊕_r {relations among the factors 3,…,T+1}, i.e. Q copies of the
   T-period moment space of the system with blocks 3,…,T+1 (in the roles of 2,…,T); by induction its
   dimension is Q c_T.
3. With k = T − 1 ∈ [1, Q − 1] blocks 3,…,T+1 and J := J^{(T−1)}: V' ⊆ J, and L_{2r} vanishes identically
   on no stratum (genericity), so by (4.1) g_r ∈ J_{(T−1)Q}. Conversely, by Lemma 4.1,
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

All genericity conditions used are independence conditions of at most Q distinct forms from
{η_i} ∪ {L_{tr}}, so sec. 2 applies.

## 6. Proof of Theorem B (independence)

By Theorem A, a family of ℓ(Q, T) elements of M_T is a basis iff it is linearly independent.

**T = 3 (DHW Proposition 2).** The Q moments (45) are m_q = 1{y_1 = q} − 1{y_2 = q} S(y) with S the
likelihood ratio of the reverse cycle; at the path y_q = (q, q, c_q), c_q ≠ q, m_{q'}(y_q) = δ_{qq'}(1 − S(y_q)),
and S(y_q) ≠ 1 generically. (We only cite this; it is DHW's proof.)

**T = 4, Q ≥ 3.** Use one-based periods. The (24) moments at T = 4 are (DHW footnote 7):
j = 0: s_1 = 1, s_2 ∈ {2, 3}, q_0 ∈ [Q] (2Q moments); j = 1: shared t ∈ {1, 2, 3} (no restriction since
Q − 2 ≥ 1), {s_1 < s_2} = {1,2,3} ∖ {t}, (q_0, q_1) ∈ [Q]^2 (3Q^2 moments). With p^σ the transformed
model (DHW (11), (13)), p^σ(y) = K_1(y_0, y_{τ(1)}) Π_{k=2}^4 K_{τ(k−1)+1}(y_{τ(k−1)}, y_{τ(k)}) for the
generation order τ, and m · p = 1{shared}[1{y_{s_1}=q_0} p^{σ_1} − 1{y_{s_2}=q_0} p^{σ_2}].

*Lifts.* For t = 1 the moment is 1{y_1 = q_1} times the T = 3 moment (45) of the chain started at
q_1 (periods 2–4); for fixed q_1 these Q moments are independent (Prop. 2 with initial state q_1),
and different q_1 have disjoint supports: the Q^2 lifts are independent.

*Quotient map.* C(m)_i := Σ_{y : y_1 = i} m(y) p_y(η). C kills every lift (the T = 3 moment has zero
conditional mean given y_1). Summing the generation-order products (stochastic rows sum to 1):

| moment | τ_1, τ_2 | C(m) |
|---|---|---|
| j = 1, t = 2, (s_1, s_2) = (1, 3) | (2,1,3,4), (2,3,1,4) | K_1(y_0,a) K_3(a,b) e_b (I − K_4), a = q_1, b = q_0 |
| j = 1, t = 3, (s_1, s_2) = (1, 2) | (3,1,2,4), (3,2,1,4) | K_1(y_0,a) K_4(a,b) e_b (I − K_3) |
| j = 0, s_2 = 2 | (1,3,2,4), (2,3,1,4) | K_1(y_0,q) e_q (I − K_3 K_4) |
| j = 0, s_2 = 3 | (1,2,3,4), (3,2,1,4) | K_1(y_0,q) e_q (I − K_4 K_3) |

(Example, first row: the τ_1 term is δ_{i q_0} K_1(y_0,q_1) K_3(q_1,q_0) after summing y_3, y_4; the τ_2 term
is K_1(y_0,q_1) K_3(q_1,q_0) K_4(q_0, i) after summing y_4.) Since K_1(y_0, a) = (π_1(a,y_0)/L_{1 y_0}) η_a,
up to the common nonzero factor 1/L_{1,y_0} and nonzero constants these are
B_{3,4,a,b}, B_{4,3,a,b}, J_{3,q}, J_{4,q} with h_{tab} := η_a K_t(a,b) e_b, B_{t,s,a,b} := h_{tab}(I − K_s),
E_{s,q} := η_q e_q (I − K_s), and J_{3,q} = E_{3,q} + Σ_d B_{3,4,q,d}, J_{4,q} = E_{4,q} + Σ_d B_{4,3,q,d}
(as η_q e_q K_3 = Σ_d h_{3qd}).

*Independence of {E_{3,q}, E_{4,q}, B_{3,4,a,b}, B_{4,3,b,a}}* (2Q + 2Q^2 vector functions). In a relation,
multiply by L_{3a} L_{4b} and restrict to Z := {L_{3a} = L_{4b} = 0} (codimension 2). Every E and every
B_{3,4,a',b'}, B_{4,3,b',a'} with (a',b') ≠ (a,b) keeps a factor L_{3a} or L_{4b} and vanishes on Z; there
L_{3a}L_{4b} B_{3,4,a,b} = −A_3(a,b) η_a η_b v_{4b} and L_{3a}L_{4b} B_{4,3,b,a} = −A_4(b,a) η_a η_b v_{3a}, with
v_{ta}(η) := (A_t(a,i) η_i)_i and A_t(a,i) = π_t(i,a). Generically η_a η_b ≢ 0 on Z and v_{4b}, v_{3a} are not
proportional on Z (independence conditions of sec. 2: {L_{3a}, L_{4b}, η_a}, {L_{3a}, L_{4b}, η_b}, and at a point
of Z with all η_i ≠ 0, non-proportionality of the rows A_3(a,·), A_4(b,·)), so both coefficients vanish.
Then the single residue along {L_{3q} = 0} (resp. L_{4q}) isolates E_{3,q} (resp. E_{4,q}). Finally the
column operation J ↦ E is unitriangular.

*Conclusion.* A relation among all ℓ(Q,4) = 3Q^2 + 2Q moments maps under C to a relation among the new
images, so all new coefficients vanish; the remaining relation among the lifts is trivial. With
Theorem A (dim M_4 = 3Q^2 + 2Q, T = 4 ≤ Q + 1) the family is a basis. ∎

## 7. Machine checks (exploration/, run with math/.venv/bin/python)

* `hq_fresh_generalQ_T3.py`: Lemma 3.1 (i)–(iii) for Q = 3..6 and dim M_3 = Q from raw likelihoods.
* `hq_fresh_generalQ_T4.py`: two-block lemma, I(B_3 ∪ B_4) vs the fat ideal, dim S_1H_3H_4 = Q^3 − Q,
  raw dim M_4 = 3Q^2 + 2Q (Q = 3, 4, 5).
* `hq_fresh_generalQ_dim.py`: Lemma 4.1 for (Q,k) = (3,1),(3,2),(4,2),(4,3),(5,2),(5,3) (fat conditions
  by all partial derivatives at random points of every stratum, at the witness point) and raw
  dim M_T = ℓ(Q,T) for (Q,T) up to (5,5), with distinct covariates.
* `hq_fresh_generalQ_quotient.py`: the quotient images of sec. 6 by brute-force path sums
  (Q = 3, 4; T = 4, 5); `hq_fresh_generalQ.py`: full rank of the raw (24) family at economic points.

Exactness: all checks are exact modular arithmetic modulo 2^61 − 1 at the stated points; they test the
lemmas at particular points and are not part of the proof.

## 8. Review

(to be recorded)

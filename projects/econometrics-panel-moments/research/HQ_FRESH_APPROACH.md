# A fresh approach to det H_q (full equation-(24) independence, Q = 3)

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

## 2. Route chosen

[to be filled as the work proceeds]

## 3. Routes tried and why they failed

[to be filled]

## 4. Remaining obstruction

[to be filled]

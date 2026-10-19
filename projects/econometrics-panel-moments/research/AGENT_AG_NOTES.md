# Agent AG notes: induction past the head map (20 Oct 2026)

Angle: an inductive proof of det R_n != 0 (product form) that circumvents the head map
Lambda_n. Labels: PROVED (argument given here), EXACT-CHECKED (exact arithmetic mod
p = 2^61-1 or exact over Q with l-adic valuations, l = 10007, at random product-form points;
single points, so evidence, not proof), CONJECTURE, REFUTED.

Scripts (run from `exploration/` with `../../../.venv/bin/python <script>`):

| script | checks | runtime |
|---|---|---|
| `agent_ag_lib.py` | shared library: term-list vectors, {E,F}-coordinates by evaluation, Lambda_n, single and double residues; self-test | 1 s |
| `agent_ag_qform.py` | identities 1.1, 1.2, 1.3 (Q1-Q3) | 1 s |
| `agent_ag_headmap.py` | tests 2.1-2.3 and 3.1-3.2 (T1-T4) | 1 min |
| `agent_ag_exchange.py` | split 4.1 and its factorisation 4.2 | 20 s |
| `agent_ag_collision.py` | latest-pair collision 5.1-5.4 (`--smith`, `--intrinsic`, `--param nu,1`) | 20 s each |

## 1. Exact identities

**1.1 Head-body form of the append map (PROVED, EXACT-CHECKED n = 2,3,4).** With
H(w) := sum_tab Lambda_n(w)_tab h_tab (a combination of heads, not zero-sum),

    Phi_n(w) = w K_N + sum Lambda_n(w)_tab B_{t,N,a,b} = H(w) + (w - H(w)) K_N.

Proof: B_{t,N,a,b} = h_tab (I - K_N). So the append keeps the head part and right-multiplies
the "body" w - H(w) by K_N. For F = h(I - W): head h, body -hW; for E_{s,a}: head
-X_a e_a K_s, body X_a e_a.

**1.2 Propagation of the head map (PROVED, EXACT-CHECKED n = 2,3,4).**
Lambda_{n+1}(Phi_n(w)) = (Lambda_n(w) on old heads, eps_n(w) on head N), where
eps_n(w)_a := sum_s e_{s,a}(w) (sum of E-coefficients). Also Lambda_{n+1} of a new column is
its unit vector and Lambda_{n+1}(E_{N,a}) = -(spread). Proof: Phi_n(F) = F',
Phi_n(E_{s,a}) = E_{s,a} - E_{N,a}; read off coefficients. Moreover eps_{n+1} o Phi_n = 0.
So (Lambda, eps) propagate trivially along the append; the obstruction is only that the
decomposition W_{n+1} = Phi_n(W_n) + E_N + new columns is what is to be proved.

**1.3 Head space and an equivalent form of the goal (PROVED, EXACT-CHECKED n = 2..5).**
Head_n := span{h_tab} (9n-dim). Head_n cap W_n = span{E_{t,a} - E_{t',a}} (dim 3n-3), because
sum_b h_tab = X_a e_a K_t and X_a e_a (K_t - K_t') = E_{t',a} - E_{t,a}; hence
dim(W_n + Head_n) = 9n^2 + 3. Then

    P(n) [ {E} u {F} basis of W_n ]  <=>  Q(n): the 9n^2 + 3 functions
    {h_tab} u {h_tab W_{t,s}} u {X_a e_a}  (heads, "bodies", coordinate vectors) are independent.

Proof: write h W = h - F and X_a e_a = E_{0,a} + sum_b h_{0ab}; a dependency splits into a Head
part and a W_n part, which must lie in Head cap W_n; P(n) then forces all coefficients to vanish;
the converse is the same bookkeeping. Given P(n), V'_n := W_n + Head_n = Head_n (+) Bod_n with
Bod_n = span(bodies, X_a e_a), and **Lambda_n is the projection onto Head_n along Bod_n**. Bodies
append exactly (beta -> beta K_N); heads and X_a e_a do not, which is where Lambda re-enters.
(Numerics note: this non-zero-sum space needs about (9n^2 - 6n)/2 evaluation points, since
its sum-of-components part is only (6n+3)-dimensional and later points add rank 2 each.)

**1.4 Vertex suffix expansion (PROVED).** Put N_u := K_u - 1 e_0^T (zero row sums, vanishes at
the vertex e_0, where every K_u = 1 e_0^T). For any row vector x and word W = K_{w1}...K_{wm},
exactly

    x (I - W) = (x - (x.1) e_0) - (x.1) sum_{proper suffixes s of W} e_0 N_s - x N_W.

(N P = 0 for P = 1 e_0^T kills every term with an N before a P.) Hence the r-jet at a vertex
of a word vector depends only on the head and the last r letters of the word. In product form
the first-order action of block u at e_0 on the zero-sum plane is z -> z Gamma diag(lambda_u x,
mu_u y) with Gamma a fixed 2x2 matrix built from g. Old columns F' have last letter N (seen at
first order); the new columns F_{t,N} have N first (invisible below order n). Not used further.

## 2. Idea (a): an invariant description of Lambda_n

**2.1 (EXACT-CHECKED n = 3,4)** Lambda_n(h_tab (I - W)) = e_tab holds exactly for the DHW words
W_{t,s} and for no other word (n = 3: 2/4 words; n = 4: 3/15). Lambda is tied to the DHW words.

**2.2 (EXACT-CHECKED n = 3,4,5)** Lambda_n restricted to W_{[n]-t} (no poles on block t) is
injective at n = 3 and surjective (rank 9n) at n = 4, 5, for every t.

**2.3 No local residue description (REFUTED, n = 3,4,5).** For every line L_uc, the residues
along L_uc of ker Lambda_n have rank 6n - 5 = rank of the residues of all of W_n. So no
functional "residue along one line at a point" vanishes on ker Lambda_n. Same at the
specialisations: economic geometric u_t = (1,2,5)^(t+1) (n = 3,4), conic u_t = (1,s_t,s_t^2),
Moebius-type u_{t+1}(i) = tau_i u_t(i) / (1 + z_i u_t(i)) (the analogue of the invariant-tail
relation), n = 4. **Kill criterion met for (a) in this form** (n = 3,4: no drop anywhere).
The only invariant points I found are the coordinate vertices (all K_u reset there, 1.4); jets
there depend on word suffixes, but Lambda is dense and global (2.1-2.3), so no fixed-complexity
description of Lambda_n emerged.

## 3. Idea (c): differential Horace at the newest vertex (u_N(0) -> 0)

**3.1 (EXACT-CHECKED n = 3,4)** With K0_N the limit kernel (never enters state 0),
V0 := {w in W_n : rho_P(w) K0_N(P) = 0 at all old cross points} has dim 3n(3n-1)/2 (one
condition per old cross point), Lambda_n|V0 has full rank 9n, and
dim(V0 cap ker Lambda_n) = 3n + 9n(n-3)/2 = the number of +1 Smith exponents found earlier.
So the order-1 problem lives on V0 cap ker Lambda_n: the "special subspace" is V0.

**3.2 (REFUTED at n = 4)** Lambda_n|V0 is not in the span of the residues of w along L_ta at the
limit new cross points P0_tab = L_ta cap L0_Nb (rank 62 on the 66-dim V0, 66 with Lambda); at
n = 3 those residues already span all of V0* (36), so n = 3 is uninformative. The restriction
is not local in this sense; the kill criterion for (c) is met at n = 4.

## 4. Exchange split of the append step

**4.1 (PROVED, EXACT-CHECKED n = 2,3,4)** The mixed family M_{n+1} = {E, F', B_{t,N,a,b},
F_{N,s,a,b}} has a block-lower-triangular canonical matrix: rows (old | N_h | N_s), columns
(F' | F_{N,s} | B_{t,N}) give [[Gamma R_n, *, 0], [0, D_N, 0], [*, *, I]] by (A1), (A2), the
unit-vector property of B_{t,N}, and c_Na = X_a L_Na' L_Na'' vanishing on L_Na', L_Na''. Here
D_N = (+)_a D_{N,a}, D_{N,a} = normal components along L_Na of the old j=0 span J^[n] (a
Lambda-free collocation). Since F_{t,N,a,b} = B_{t,N,a,b} + h_tab K_N (I - Pi_(t)):

    det R_{n+1} = +- det Gamma * det R_n * det D_N * det(I + C_n),

C_n = B_{t,N}-coordinates of h_tab K_N (I - Pi_(t)) in the basis M_{n+1}.

**4.2 (EXACT-CHECKED n = 2, along u_N(1), 300-400 values)** The denominator of det(I + C_n)
coincides with the numerator of det R^M_{n+1} (gcd of full degree 30; non-linear factor degrees
2,2,3,5,7, i.e. the non-natural part of det D_N), and the numerator of det(I + C_n) is a perfect
cube Phi^3 (irreducible factors of degrees 2,2,3,5, each with multiplicity 3): the collocation
cancels and the exchange factor carries the whole irreducible cofactor. C_n contains Lambda_n (its N_s rows involve head sums), so this split
does not circumvent the head map. Killed.

## 5. New: collision of the two latest blocks is a clean first-order degeneration

Configuration: u_N = u_{N-1} (1 + delta nu), delta = l, old blocks and nu generic.

**5.1 (EXACT-CHECKED m = 3,4,5,6 blocks)** Canonical Smith exponents of R_m:
-1^(9m-15), 0^(...), +1^(9m-15), sum 0. So v(det R_m) = 0: unlike every torus degeneration of
the newest block, the latest-pair collision keeps det R_m finite and nonzero in the limit.

**5.2 (EXACT-CHECKED m = 3,4,5)** Coordinate-free Smith exponents of the evaluation matrix of
{E} u {F} at fixed generic points: only 0 and 1, with exactly 18m - 24 ones (30, 48, 66). This
equals the number of family pairs that coincide at delta = 0: (F_{t,N-1}, F_{t,N}) and
(F_{N-1,s}, F_{N,s}) for t, s not in {N-1,N} (9(m-2) each), (F_{N-1,N}, F_{N,N-1}) (9) and
(E_{N-1,a}, E_{N,a}) (3). Hence (the pair differences span the delta = 0 kernel):

    Coll(m): the delta = 0 family (one member per coinciding pair) together with the
    first-order jets d/d delta of the 18m-24 pair differences is linearly independent.

Coll(m) implies P(m) (semicontinuity). CONJECTURE: Coll(m) for all m. The jets are explicit,
e.g. d/d delta (F_{t,N} - F_{t,N-1}) = h_tab (K Pi' D - D Pi' K) with K = K_{N-1},
D = d K_N / d delta (simple and double poles on block N-1's lines), linear in nu.

**5.3 (PROVED, given P(m-1); dimension EXACT-CHECKED via 5.2)** The delta = 0 span is
S_0 = Phi0(W_{m-1}) + span{E_{N-1,a}} + span{h_{N-1,ab}(I - K Pi_{0..N-2})}, where
Phi0(w) = w K + sum Lambda_{m-1}(w) h (I - K) appends block N-1 to itself. Note
Phi0(E_{N-1,a}) = 0, and Phi0 o Phi_{m-2} appends K^2:
Phi0(Phi_{m-2}(v)) = v K^2 + sum Lambda_{m-2}(v) h (I - K^2) + sum_a eps_{m-2}(v)_a X_a e_a K (I - K).
dim S_0 = 9m^2 - 24m + 24 = (number of family members) - (18m - 24), as 5.2 requires.

**5.4 (EXACT-CHECKED m = 3,4)** No product formula: lim det R_m / det R_{m-1}(0..m-2), as a
function of nu_1, has numerator factor degrees [2,2,2,4,4,4] (m = 3, the known cube) and
[1,1,1,3,3,3,6,6,12] (m = 4). The leading term is not natural, so a direct multiplicative
recursion through the collision is killed; the structural statement Coll(m) survives.

**5.5** Collisions of 3 to 5 latest blocks: canonical coordinates blow up (exponent sums
-30 ... -252), so canonical data says nothing there. Coordinate directions nu = e_i are
inadmissible (the same-colour cross point L_{N-1,a} cap L_{N,a} lies on X_i = 0).

## 6. Assessment and next step

What survived: the identities of section 1 (PROVED); the latest-pair collision as a clean
degeneration with explicitly known first-order kernel (5.2, EXACT-CHECKED m <= 5, canonical
m <= 6). Killed here: local or invariant descriptions of Lambda_n (2.3, 3.2), the exchange
split (4.2), and product-formula recursion through the collision (5.4).

Most promising next step: prove Coll(m) from P(m-1). By 5.3 the delta = 0 span S_0 is the
self-append of the (m-1)-system plus 12 explicit extra directions. The step is invertibility
of the order-1 map (jets of the 18m-24 pair differences) -> W0_m / S_0, which is linear in nu.
Two concrete tasks: (i) compute W0_m / S_0 intrinsically (flat limit with doubled lines of
block N-1; the double-pole coefficients of S_0 and of the jets are both longitudinal, so the
transverse simple-pole and second-order data along the doubled lines are the candidate
coordinates); (ii) test whether the order-1 matrix is block-triangular by pair type
((t, N-1/N), (N-1/N, s), (N-1, N), E). If (i) gives a Lambda-free quotient, this is the induction
the brief asks for. Iterating collisions leads to the full coalescence limit (another agent's
`hq_fresh_coalesce.py`); 5.2 suggests checking whether that limit is also exactly first-order
per coinciding pair.

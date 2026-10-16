import PanelMoments.SourceHomogeneous
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv

set_option autoImplicit false

/-!
# Exact source cancellation at a rank-one prepend

The head terms and both ordered singleton columns are retained in the
identity E_t - E_s + ∑ b, (T_ts - T_st) = -X_a e_a [K_t,K_s] V.
The existing canonical word order puts a prepended block at the start of
V. A row-stochastic commutator annihilates Π = 1 e₀, so this exact
combination of actual homogeneous source columns vanishes at the
rank-one prepend.

The curve changes only actual time 2 to G diag(1, εu, εv).
Its componentwise derivative, and the first derivative of the actual
source combination, are proved with explicit baseline denominator units.
These are source identities, not an independence or rank theorem.
-/

namespace PanelMoments.SourceRankOnePrepend

open scoped BigOperators
open SourceHomogeneous SourceTransferOrders

noncomputable section

def pairColumn (X : State 2 → ℝ)
    (K L V : Matrix (State 2) (State 2) ℝ) (a b c : State 2) : ℝ :=
  X a * K a b * ((if b = c then 1 else 0) - (L * V) b c)

def orderedPairCombination (X : State 2 → ℝ)
    (K L V : Matrix (State 2) (State 2) ℝ) (a c : State 2) : ℝ :=
  X a * ((if a = c then 1 else 0) - K a c) -
    X a * ((if a = c then 1 else 0) - L a c) +
    ∑ b, (pairColumn X K L V a b c - pairColumn X L K V a b c)

theorem sum_pairColumn (X : State 2 → ℝ)
    (K L V : Matrix (State 2) (State 2) ℝ) (a c : State 2) :
    ∑ b, pairColumn X K L V a b c =
      X a * (K a c - (K * (L * V)) a c) := by
  simp only [pairColumn, mul_sub, Finset.sum_sub_distrib, mul_assoc,
    ← Finset.mul_sum, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [Matrix.mul_apply]

/-- The cancellation needs neither stochasticity nor commutativity of the kernels. -/
theorem orderedPairCombination_eq_commutator (X : State 2 → ℝ)
    (K L V : Matrix (State 2) (State 2) ℝ) (a c : State 2) :
    orderedPairCombination X K L V a c =
      -X a * (((K * L - L * K) * V) a c) := by
  rw [orderedPairCombination, Finset.sum_sub_distrib, sum_pairColumn, sum_pairColumn]
  have hm : ((K * L - L * K) * V) a c =
      (K * (L * V)) a c - (L * (K * V)) a c := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    rfl
  rw [hm]
  ring

def remainingProduct {N : ℕ} (A : Table 2) (X : State 2 → ℝ) (t s : Fin N) :
    Matrix (State 2) (State 2) ℝ :=
  homogeneousWordProduct A X (((Finset.univ.erase t).erase s).sort (· ≤ ·))

theorem remainingProduct_comm {N : ℕ} (A : Table 2) (X : State 2 → ℝ)
    (t s : Fin N) : remainingProduct A X t s = remainingProduct A X s t := by
  have he : (Finset.univ.erase t).erase s = (Finset.univ.erase s).erase t := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact and_comm
  simp only [remainingProduct, he]

theorem singletonVector_eq_pairColumn {N : ℕ} (A : Table 2) (X : State 2 → ℝ)
    (t : Fin N) (s : {s : Fin N // s ≠ t}) (a b c : State 2) :
    singletonVector A X t s a b c =
      pairColumn X (kernel A X (t.val + 2)) (kernel A X (s.val.val + 2))
        (remainingProduct A X t s.val) a b c := by
  rfl

def sourcePairCombination {N : ℕ} (A : Table 2) (X : State 2 → ℝ)
    (t s : Fin N) (hts : t ≠ s) (a c : State 2) : ℝ :=
  singleBlockVector A X t a c - singleBlockVector A X s a c +
    ∑ b, (singletonVector A X t ⟨s, Ne.symm hts⟩ a b c -
      singletonVector A X s ⟨t, hts⟩ a b c)

/-- The matrices are the actual homogeneous kernels in the actual singleton words. -/
theorem sourcePairCombination_eq_commutator {N : ℕ} (A : Table 2)
    (X : State 2 → ℝ) (t s : Fin N) (hts : t ≠ s) (a c : State 2) :
    sourcePairCombination A X t s hts a c =
      -X a * (((kernel A X (t.val + 2) * kernel A X (s.val + 2) -
        kernel A X (s.val + 2) * kernel A X (t.val + 2)) *
          remainingProduct A X t s) a c) := by
  unfold sourcePairCombination
  simp only [singletonVector_eq_pairColumn]
  rw [remainingProduct_comm A X s t]
  exact orderedPairCombination_eq_commutator X _ _ _ a c

def oldSuffixProduct {N : ℕ} (A : Table 2) (X : State 2 → ℝ)
    (t s : Fin (N + 1)) : Matrix (State 2) (State 2) ℝ :=
  homogeneousWordProduct A X
    ((((Finset.univ.erase t).erase s).erase 0).sort (· ≤ ·))

/-- Since slot zero is least, it precedes the unchanged old suffix. -/
theorem remainingProduct_eq_prepend {N : ℕ} (A : Table 2) (X : State 2 → ℝ)
    (t s : Fin (N + 1)) (ht : t ≠ 0) (hs : s ≠ 0) :
    remainingProduct A X t s = kernel A X 2 * oldSuffixProduct A X t s := by
  have hm : (0 : Fin (N + 1)) ∈ (Finset.univ.erase t).erase s := by
    simp [Ne.symm ht, Ne.symm hs]
  have hle : ∀ u ∈ ((Finset.univ.erase t).erase s).erase (0 : Fin (N + 1)),
      (0 : Fin (N + 1)) ≤ u := by
    intro u _
    exact Fin.zero_le u
  have hsort : ((Finset.univ.erase t).erase s).sort (· ≤ ·) =
      0 :: (((Finset.univ.erase t).erase s).erase 0).sort (· ≤ ·) := by
    rw [← Finset.sort_insert (· ≤ ·) hle (by simp)]
    rw [Finset.insert_erase hm]
  simp only [remainingProduct, hsort, homogeneousWordProduct, List.map_cons,
    List.prod_cons, Fin.val_zero, zero_add, oldSuffixProduct]

/-- The rank-one row-stochastic projection 1 e₀. -/
def collapseMatrix : Matrix (State 2) (State 2) ℝ :=
  Matrix.of (fun _ c => if c = 0 then 1 else 0)

theorem stochastic_mul_collapse (K : Matrix (State 2) (State 2) ℝ)
    (hK : ∀ a, ∑ b, K a b = 1) : K * collapseMatrix = collapseMatrix := by
  ext a c
  by_cases hc : c = 0
  · subst c
    simpa [Matrix.mul_apply, collapseMatrix] using hK a
  · simp [Matrix.mul_apply, collapseMatrix, hc]

theorem commutator_mul_collapse (K L : Matrix (State 2) (State 2) ℝ)
    (hK : ∀ a, ∑ b, K a b = 1) (hL : ∀ a, ∑ b, L a b = 1) :
    (K * L - L * K) * collapseMatrix = 0 := by
  rw [Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    stochastic_mul_collapse L hL, stochastic_mul_collapse K hK,
    stochastic_mul_collapse L hL]
  exact sub_self _

theorem kernel_row_sum_of_rowForm_ne_zero {Q : ℕ} (A : Table Q)
    (X : State Q → ℝ) (t : ℕ) (a : State Q) (h : rowForm A X t a ≠ 0) :
    ∑ b, kernel A X t a b = 1 := by
  simp only [kernel, Matrix.of_apply, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ h

/-- Exact collapse, with denominator units only for the two old kernels. -/
theorem sourcePairCombination_zero_of_collapse {N : ℕ} (A : Table 2)
    (X : State 2 → ℝ) (t s : Fin (N + 1)) (hts : t ≠ s)
    (ht : t ≠ 0) (hs : s ≠ 0) (a c : State 2)
    (hcollapse : kernel A X 2 = collapseMatrix)
    (hLt : ∀ i, rowForm A X (t.val + 2) i ≠ 0)
    (hLs : ∀ i, rowForm A X (s.val + 2) i ≠ 0) :
    sourcePairCombination A X t s hts a c = 0 := by
  rw [sourcePairCombination_eq_commutator, remainingProduct_eq_prepend A X t s ht hs,
    hcollapse, ← Matrix.mul_assoc]
  rw [commutator_mul_collapse _ _
    (fun i => kernel_row_sum_of_rowForm_ne_zero A X _ i (hLt i))
    (fun i => kernel_row_sum_of_rowForm_ne_zero A X _ i (hLs i))]
  simp

/-- The only changed time block is the prepended one, actual time 2. -/
def prependTable (A : Table 2) (G : Matrix (State 2) (State 2) ℝ)
    (u v ε : ℝ) : Table 2 :=
  fun t i j => if t = 2 then G i j * (![1, ε * u, ε * v] : State 2 → ℝ) j
    else A t i j

theorem prependTable_other (A : Table 2) (G : Matrix (State 2) (State 2) ℝ)
    (u v ε : ℝ) (t : ℕ) (ht : t ≠ 2) : prependTable A G u v ε t = A t := by
  funext i j
  simp [prependTable, ht]

theorem rowForm_prependTable (A : Table 2) (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (u v ε : ℝ) (i : State 2) :
    rowForm (prependTable A G u v ε) X 2 i =
      G i 0 * X 0 + ε * (G i 1 * u * X 1 + G i 2 * v * X 2) := by
  simp [rowForm, prependTable, Fin.sum_univ_succ]
  ring

def baseNumerator (G : Matrix (State 2) (State 2) ℝ) (X : State 2 → ℝ)
    (i : State 2) : State 2 → ℝ := ![G i 0 * X 0, 0, 0]

def jetNumerator (G : Matrix (State 2) (State 2) ℝ) (X : State 2 → ℝ)
    (u v : ℝ) (i : State 2) : State 2 → ℝ :=
  ![0, G i 1 * u * X 1, G i 2 * v * X 2]

theorem kernel_prependTable (A : Table 2) (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (u v ε : ℝ) (i j : State 2) :
    kernel (prependTable A G u v ε) X 2 i j =
      (baseNumerator G X i j + ε * jetNumerator G X u v i j) /
        (G i 0 * X 0 + ε * (G i 1 * u * X 1 + G i 2 * v * X 2)) := by
  simp only [kernel, Matrix.of_apply, rowForm_prependTable, prependTable, ↓reduceIte]
  congr 1
  fin_cases j <;> simp [baseNumerator, jetNumerator] <;> ring

theorem kernel_prependTable_zero (A : Table 2) (G : Matrix (State 2) (State 2) ℝ)
    (X : State 2 → ℝ) (u v : ℝ)
    (hG : ∀ i, G i 0 ≠ 0) (hX : X 0 ≠ 0) :
    kernel (prependTable A G u v 0) X 2 = collapseMatrix := by
  ext i j
  rw [kernel_prependTable]
  fin_cases j <;> simp [baseNumerator, collapseMatrix, hG i, hX]

def prependJet (G : Matrix (State 2) (State 2) ℝ) (X : State 2 → ℝ)
    (u v : ℝ) : Matrix (State 2) (State 2) ℝ :=
  Matrix.of (fun i =>
    let α := G i 1 * u * X 1 / (G i 0 * X 0)
    let β := G i 2 * v * X 2 / (G i 0 * X 0)
    ![-α - β, α, β])

/-- The derivative has rows (-α-β, α, β), with the actual homogeneous units. -/
theorem kernel_prependTable_hasDerivAt (A : Table 2)
    (G : Matrix (State 2) (State 2) ℝ) (X : State 2 → ℝ) (u v : ℝ)
    (i j : State 2) (hG : G i 0 ≠ 0) (hX : X 0 ≠ 0) :
    HasDerivAt (fun ε : ℝ => kernel (prependTable A G u v ε) X 2 i j)
      (prependJet G X u v i j) 0 := by
  have hn : HasDerivAt
      (fun ε : ℝ => baseNumerator G X i j + ε * jetNumerator G X u v i j)
      (jetNumerator G X u v i j) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
      (jetNumerator G X u v i j)).const_add (baseNumerator G X i j)
  have hd : HasDerivAt
      (fun ε : ℝ => G i 0 * X 0 + ε * (G i 1 * u * X 1 + G i 2 * v * X 2))
      (G i 1 * u * X 1 + G i 2 * v * X 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const
      (G i 1 * u * X 1 + G i 2 * v * X 2)).const_add (G i 0 * X 0)
  have hq := hn.fun_div hd (by simpa using mul_ne_zero hG hX)
  have hc :
      (jetNumerator G X u v i j * (G i 0 * X 0) -
        baseNumerator G X i j * (G i 1 * u * X 1 + G i 2 * v * X 2)) /
          (G i 0 * X 0) ^ 2 = prependJet G X u v i j := by
    fin_cases j <;> simp [jetNumerator, baseNumerator, prependJet]
    all_goals field_simp [hG, hX] <;> ring
  have hq' : HasDerivAt
      (fun ε : ℝ => (baseNumerator G X i j + ε * jetNumerator G X u v i j) /
        (G i 0 * X 0 + ε * (G i 1 * u * X 1 + G i 2 * v * X 2)))
      (prependJet G X u v i j) 0 := by
    simpa only [zero_mul, add_zero, hc] using hq
  apply hq'.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall (fun ε => kernel_prependTable A G X u v ε i j)

theorem prependTable_oldKernel {N : ℕ} (A : Table 2)
    (G : Matrix (State 2) (State 2) ℝ) (X : State 2 → ℝ) (u v ε : ℝ)
    (t : Fin (N + 1)) (ht : t ≠ 0) :
    kernel (prependTable A G u v ε) X (t.val + 2) = kernel A X (t.val + 2) := by
  simp [kernel, rowForm, prependTable, ht]

theorem oldSuffixProduct_prependTable {N : ℕ} (A : Table 2)
    (G : Matrix (State 2) (State 2) ℝ) (X : State 2 → ℝ) (u v ε : ℝ)
    (t s : Fin (N + 1)) :
    oldSuffixProduct (prependTable A G u v ε) X t s = oldSuffixProduct A X t s := by
  unfold oldSuffixProduct homogeneousWordProduct
  apply congrArg List.prod
  apply List.map_congr_left
  intro k hk
  have hk' : k ∈ ((Finset.univ.erase t).erase s).erase (0 : Fin (N + 1)) := by
    simpa only [Finset.mem_sort] using hk
  have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk').1
  exact prependTable_oldKernel A G X u v ε k hk0

/-- Exact finite-parameter source factorization with every old factor fixed. -/
theorem sourcePairCombination_prependTable {N : ℕ} (A : Table 2)
    (G : Matrix (State 2) (State 2) ℝ) (X : State 2 → ℝ) (u v ε : ℝ)
    (t s : Fin (N + 1)) (hts : t ≠ s) (ht : t ≠ 0) (hs : s ≠ 0)
    (a c : State 2) :
    sourcePairCombination (prependTable A G u v ε) X t s hts a c =
      -X a * (((kernel A X (t.val + 2) * kernel A X (s.val + 2) -
        kernel A X (s.val + 2) * kernel A X (t.val + 2)) *
          kernel (prependTable A G u v ε) X 2 * oldSuffixProduct A X t s) a c) := by
  rw [sourcePairCombination_eq_commutator,
    remainingProduct_eq_prepend _ X t s ht hs,
    prependTable_oldKernel A G X u v ε t ht,
    prependTable_oldKernel A G X u v ε s hs,
    oldSuffixProduct_prependTable, Matrix.mul_assoc]

/-- Matrix multiplication by fixed old factors preserves the exact first jet. -/
theorem fixedMatrix_prepend_hasDerivAt (A : Table 2)
    (G C R : Matrix (State 2) (State 2) ℝ) (X : State 2 → ℝ) (u v : ℝ)
    (a c : State 2) (hG : ∀ i, G i 0 ≠ 0) (hX : X 0 ≠ 0) :
    HasDerivAt
      (fun ε : ℝ => -X a * ((C * kernel (prependTable A G u v ε) X 2 * R) a c))
      (-X a * ((C * prependJet G X u v * R) a c)) 0 := by
  simp only [Matrix.mul_apply]
  exact (HasDerivAt.fun_sum (fun j _ =>
    (HasDerivAt.fun_sum (fun i _ =>
      (kernel_prependTable_hasDerivAt A G X u v i j (hG i) hX).const_mul
        (C a i))).mul_const (R j c))).const_mul (-X a)

/-- The actual source first jet is -X_a e_a [K_t,K_s] H R_ts. -/
theorem sourcePairCombination_prepend_hasDerivAt {N : ℕ} (A : Table 2)
    (G : Matrix (State 2) (State 2) ℝ) (X : State 2 → ℝ) (u v : ℝ)
    (t s : Fin (N + 1)) (hts : t ≠ s) (ht : t ≠ 0) (hs : s ≠ 0)
    (a c : State 2) (hG : ∀ i, G i 0 ≠ 0) (hX : X 0 ≠ 0) :
    HasDerivAt
      (fun ε : ℝ => sourcePairCombination (prependTable A G u v ε) X t s hts a c)
      (-X a * (((kernel A X (t.val + 2) * kernel A X (s.val + 2) -
        kernel A X (s.val + 2) * kernel A X (t.val + 2)) *
          prependJet G X u v * oldSuffixProduct A X t s) a c)) 0 := by
  apply (fixedMatrix_prepend_hasDerivAt A G _ _ X u v a c hG hX).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall
    (fun ε => sourcePairCombination_prependTable A G X u v ε t s hts ht hs a c)

end

end PanelMoments.SourceRankOnePrepend

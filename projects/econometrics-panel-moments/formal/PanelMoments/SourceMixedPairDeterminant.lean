import PanelMoments.SourceMixedPoleJet
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

/-!
# An explicit two-column determinant for the actual mixed-pair derivatives

At two vanishing row forms, the relative direction `(0, τ, ν)` and the
coordinate curve `P + ε e₀` give an explicit nonzero direction factor.
The minor of two zero-sum rows transported through a row-stochastic tail
is multiplied by the tail determinant. Combining these identities with
`SourceMixedPoleJet` gives the exact determinant of the two cleared first
derivatives, with the positive sign for the ordered pair `(S_ab, S_ba)`.

The actual-word corollary obtains tail differentiability, row sums, and
determinant nonvanishing from the existing ordered model kernels. The
result concerns this local derivative block; it does not construct a
residue operator or prove independence of the full source family.
-/

namespace PanelMoments.SourceMixedPairDeterminant

open scoped BigOperators
open SourceHomogeneous SourceRelativeTimeJet SourceLocalJetAlgebra SourceMixedPoleJet

noncomputable section

def minor01 (r s : State 2 → ℝ) : ℝ := r 0 * s 1 - r 1 * s 0

def rowMinor01 (A : Table 2) (t : ℕ) (a b : State 2) : ℝ :=
  A t a 0 * A t b 1 - A t a 1 * A t b 0

/-- The pair direction is determined by the actual row forms and relative-time
jet, rather than assumed nonzero as an abstract coefficient. -/
theorem relative_e0_pair_direction (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (τ ν : ℝ) (a b : State 2)
    (hPa : rowForm A P t a = 0) (hPb : rowForm A P t b = 0) :
    rowFormJet A P t (relativeDirection τ ν) a * rowForm A ![1, 0, 0] t b -
        rowFormJet A P t (relativeDirection τ ν) b * rowForm A ![1, 0, 0] t a =
      (ν - τ) * P 1 * rowMinor01 A t a b := by
  apply sub_eq_zero.mp
  calc
    _ = ν * (A t b 0 * rowForm A P t a - A t a 0 * rowForm A P t b) := by
      simp [rowForm, rowFormJet_relativeDirection, rowMinor01, Fin.sum_univ_succ]
      ring
    _ = 0 := by simp [hPa, hPb]

/-- On the zero-sum plane, a row-stochastic three-state matrix multiplies the
first two-coordinate minor by its full determinant. -/
theorem minor01_vecMul_of_row_sum (r s : State 2 → ℝ)
    (Q : Matrix (State 2) (State 2) ℝ)
    (hr : ∑ k, r k = 0) (hs : ∑ k, s k = 0)
    (hQ : ∀ k, ∑ l, Q k l = 1) :
    minor01 (Matrix.vecMul r Q) (Matrix.vecMul s Q) = minor01 r s * Q.det := by
  have hr' : r 0 + r 1 + r 2 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hr
  have hs' : s 0 + s 1 + s 2 = 0 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hs
  have hr2 : r 2 = -r 0 - r 1 := by linarith
  have hs2 : s 2 = -s 0 - s 1 := by linarith
  have hQ2 (k : State 2) : Q k 2 = 1 - Q k 0 - Q k 1 := by
    have hk : Q k 0 + Q k 1 + Q k 2 = 1 := by
      simpa [Fin.sum_univ_succ, add_assoc] using hQ k
    linarith
  rw [Matrix.det_fin_three Q]
  simp [minor01, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, hr2, hs2, hQ2]
  ring

theorem rowTail_pair_minor (A : Table 2) (P : State 2 → ℝ) (t : ℕ)
    (Q : Matrix (State 2) (State 2) ℝ) (a b : State 2)
    (hPa : rowForm A P t a = 0) (hPb : rowForm A P t b = 0)
    (hQ : ∀ k, ∑ l, Q k l = 1) :
    minor01 (rowTail A P t Q a) (rowTail A P t Q b) =
      (P 0 * P 1 * rowMinor01 A t a b) * Q.det := by
  have h := minor01_vecMul_of_row_sum
    (fun k => A t a k * P k) (fun k => A t b k * P k) Q hPa hPb hQ
  change minor01 (rowTail A P t Q a) (rowTail A P t Q b) = _ at h
  rw [h]
  congr 1
  simp only [minor01, rowMinor01]
  ring

/-- The actual first derivative of the cleared special numerator. -/
def clearedPairDerivative (A : Table 2) (P Y : State 2 → ℝ) (t : ℕ)
    (d : State 2 → ℝ) (Q : ℝ → Matrix (State 2) (State 2) ℝ)
    (a b : State 2) : State 2 → ℝ :=
  fun j => deriv
    (fun ε : ℝ => clearedSpecial A (affinePoint P Y ε) t d (Q ε) a b j) 0

private theorem clearedPairDerivative_apply (A : Table 2) (P Y : State 2 → ℝ)
    (t : ℕ) (d : State 2 → ℝ) (Q : ℝ → Matrix (State 2) (State 2) ℝ)
    (a b j : State 2) (hPa : rowForm A P t a = 0) (hPb : rowForm A P t b = 0)
    (hQ : ∀ k l, DifferentiableAt ℝ (fun ε : ℝ => Q ε k l) 0) :
    clearedPairDerivative A P Y t d Q a b j =
      prefixNumerator A P t a b * rowTail A P t (Q 0) b j *
        (rowFormJet A P t d a * rowForm A Y t b -
          rowFormJet A P t d b * rowForm A Y t a) :=
  (clearedSpecial_affine_hasDerivAt A P Y t d Q a b j hPa hPb hQ).deriv

/-- The two derivative rows have opposite pair factors; reversing their tail
rows supplies the second sign change, yielding the positive determinant. -/
theorem clearedPairDerivative_minor (A : Table 2) (P Y : State 2 → ℝ) (t : ℕ)
    (d : State 2 → ℝ) (Q : ℝ → Matrix (State 2) (State 2) ℝ) (a b : State 2)
    (hPa : rowForm A P t a = 0) (hPb : rowForm A P t b = 0)
    (hQ : ∀ k l, DifferentiableAt ℝ (fun ε : ℝ => Q ε k l) 0)
    (hQsum : ∀ k, ∑ l, Q 0 k l = 1) :
    minor01 (clearedPairDerivative A P Y t d Q a b)
      (clearedPairDerivative A P Y t d Q b a) =
      prefixNumerator A P t a b * prefixNumerator A P t b a *
        (rowFormJet A P t d a * rowForm A Y t b -
          rowFormJet A P t d b * rowForm A Y t a) ^ 2 *
        (P 0 * P 1 * rowMinor01 A t a b) * (Q 0).det := by
  calc
    _ = prefixNumerator A P t a b * prefixNumerator A P t b a *
        (rowFormJet A P t d a * rowForm A Y t b -
          rowFormJet A P t d b * rowForm A Y t a) ^ 2 *
        minor01 (rowTail A P t (Q 0) a) (rowTail A P t (Q 0) b) := by
      simp only [minor01,
        clearedPairDerivative_apply A P Y t d Q a b 0 hPa hPb hQ,
        clearedPairDerivative_apply A P Y t d Q a b 1 hPa hPb hQ,
        clearedPairDerivative_apply A P Y t d Q b a 0 hPb hPa hQ,
        clearedPairDerivative_apply A P Y t d Q b a 1 hPb hPa hQ]
      ring
    _ = _ := by
      rw [rowTail_pair_minor A P t (Q 0) a b hPa hPb hQsum]
      ring

theorem relativePairDerivative_minor (A : Table 2) (P : State 2 → ℝ) (t : ℕ)
    (τ ν : ℝ) (Q : ℝ → Matrix (State 2) (State 2) ℝ) (a b : State 2)
    (hPa : rowForm A P t a = 0) (hPb : rowForm A P t b = 0)
    (hQ : ∀ k l, DifferentiableAt ℝ (fun ε : ℝ => Q ε k l) 0)
    (hQsum : ∀ k, ∑ l, Q 0 k l = 1) :
    minor01 (clearedPairDerivative A P ![1, 0, 0] t (relativeDirection τ ν) Q a b)
      (clearedPairDerivative A P ![1, 0, 0] t (relativeDirection τ ν) Q b a) =
      prefixNumerator A P t a b * prefixNumerator A P t b a *
        ((ν - τ) * P 1 * rowMinor01 A t a b) ^ 2 *
        (P 0 * P 1 * rowMinor01 A t a b) * (Q 0).det := by
  rw [clearedPairDerivative_minor A P ![1, 0, 0] t (relativeDirection τ ν) Q a b
    hPa hPb hQ hQsum, relative_e0_pair_direction A P t τ ν a b hPa hPb]

theorem relativePairDerivative_minor_ne_zero (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (τ ν : ℝ) (Q : ℝ → Matrix (State 2) (State 2) ℝ) (a b : State 2)
    (hPa : rowForm A P t a = 0) (hPb : rowForm A P t b = 0)
    (hQ : ∀ k l, DifferentiableAt ℝ (fun ε : ℝ => Q ε k l) 0)
    (hQsum : ∀ k, ∑ l, Q 0 k l = 1)
    (hm : rowMinor01 A t a b ≠ 0) (hP0 : P 0 ≠ 0) (hP1 : P 1 ≠ 0)
    (hab : prefixNumerator A P t a b ≠ 0) (hba : prefixNumerator A P t b a ≠ 0)
    (hντ : ν - τ ≠ 0) (hdet : (Q 0).det ≠ 0) :
    minor01 (clearedPairDerivative A P ![1, 0, 0] t (relativeDirection τ ν) Q a b)
      (clearedPairDerivative A P ![1, 0, 0] t (relativeDirection τ ν) Q b a) ≠ 0 := by
  rw [relativePairDerivative_minor A P t τ ν Q a b hPa hPb hQ hQsum]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero hab hba)
      (pow_ne_zero 2 (mul_ne_zero (mul_ne_zero hντ hP1) hm)))
      (mul_ne_zero (mul_ne_zero hP0 hP1) hm)) hdet

/-- Row sums hold at arbitrary real coordinates with a nonzero row form,
including the nonpositive pair points needed here. -/
theorem kernel_row_sum_of_nonzero (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (a : State 2) (hL : rowForm A P t a ≠ 0) :
    ∑ b, kernel A P t a b = 1 := by
  simp only [kernel, Matrix.of_apply, div_eq_mul_inv, ← Finset.sum_mul]
  exact mul_inv_cancel₀ hL

theorem homogeneousWordProduct_row_sum_of_nonzero {N : ℕ} (A : Table 2)
    (P : State 2 → ℝ) (w : List (Fin N))
    (hL : ∀ u ∈ w, ∀ a, rowForm A P (u.val + 2) a ≠ 0) (a : State 2) :
    ∑ b, homogeneousWordProduct A P w a b = 1 := by
  revert hL a
  induction w with
  | nil =>
      intro _ a
      simp [homogeneousWordProduct, Matrix.one_apply]
  | cons u w ih =>
      intro hL a
      have hTail : ∀ v ∈ w, ∀ c, rowForm A P (v.val + 2) c ≠ 0 := by
        intro v hv c
        exact hL v (by simp [hv]) c
      change ∑ b, (kernel A P (u.val + 2) * homogeneousWordProduct A P w) a b = 1
      simp only [Matrix.mul_apply]
      rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, ih hTail, mul_one]
      exact kernel_row_sum_of_nonzero A P (u.val + 2) a (hL u (by simp) a)

/-- The actual homogeneous kernel determinant, with all coordinate and row-form
factors retained. This identity also holds when one of those factors vanishes. -/
theorem kernel_det (A : Table 2) (P : State 2 → ℝ) (t : ℕ) :
    (kernel A P t).det = (Matrix.of (A t)).det * (∏ c, P c) /
      (∏ a, rowForm A P t a) := by
  have hk : kernel A P t = Matrix.diagonal (fun a => (rowForm A P t a)⁻¹) *
      Matrix.of (A t) * Matrix.diagonal P := by
    ext a b
    simp [kernel, div_eq_mul_inv]
    ring
  rw [hk, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal]
  simp only [Finset.prod_inv_distrib, div_eq_mul_inv]
  ring

theorem homogeneousWordProduct_det {N : ℕ} (A : Table 2) (P : State 2 → ℝ)
    (w : List (Fin N)) :
    (homogeneousWordProduct A P w).det =
      (w.map (fun u => (Matrix.of (A (u.val + 2))).det * (∏ c, P c) /
        (∏ a, rowForm A P (u.val + 2) a))).prod := by
  induction w with
  | nil => simp [homogeneousWordProduct]
  | cons u w ih =>
      change (kernel A P (u.val + 2) * homogeneousWordProduct A P w).det =
        ((Matrix.of (A (u.val + 2))).det * (∏ c, P c) /
          (∏ a, rowForm A P (u.val + 2) a)) * _
      rw [Matrix.det_mul, kernel_det, ih]
      rfl

/-- A concrete nonzero two-column derivative block for the actual ordered tail.
All hypotheses are local coordinate, row-form, entry, or block-determinant units. -/
theorem actualWord_pair_minor_ne_zero {N : ℕ} (A : Table 2) (P : State 2 → ℝ)
    (t : ℕ) (τ ν : ℝ) (w : List (Fin N)) (a b : State 2)
    (hPa : rowForm A P t a = 0) (hPb : rowForm A P t b = 0)
    (hL : ∀ u ∈ w, ∀ c, rowForm A P (u.val + 2) c ≠ 0)
    (hD : ∀ u ∈ w, (Matrix.of (A (u.val + 2))).det ≠ 0)
    (hP : ∀ c, P c ≠ 0) (hm : rowMinor01 A t a b ≠ 0)
    (hab : A t a b ≠ 0) (hba : A t b a ≠ 0) (hντ : ν - τ ≠ 0) :
    minor01
      (clearedPairDerivative A P ![1, 0, 0] t (relativeDirection τ ν)
        (fun ε => homogeneousWordProduct A (affinePoint P ![1, 0, 0] ε) w) a b)
      (clearedPairDerivative A P ![1, 0, 0] t (relativeDirection τ ν)
        (fun ε => homogeneousWordProduct A (affinePoint P ![1, 0, 0] ε) w) b a) ≠ 0 := by
  have hdet : (homogeneousWordProduct A P w).det ≠ 0 := by
    rw [homogeneousWordProduct_det]
    apply List.prod_ne_zero
    intro hz
    rcases List.mem_map.mp hz with ⟨u, hu, heq⟩
    have hp : (∏ c, P c) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun c _ => hP c)
    have hl : (∏ c, rowForm A P (u.val + 2) c) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun c _ => hL u hu c)
    exact (div_ne_zero (mul_ne_zero (hD u hu) hp) hl) heq
  apply relativePairDerivative_minor_ne_zero A P t τ ν _ a b hPa hPb
    (fun k l => homogeneousWordProduct_affine_differentiableAt A P ![1, 0, 0] w hL k l)
    (by simpa only [affinePoint_zero] using
      homogeneousWordProduct_row_sum_of_nonzero A P w hL)
    hm (hP 0) (hP 1)
  · exact mul_ne_zero (mul_ne_zero hab (hP a)) (hP b)
  · exact mul_ne_zero (mul_ne_zero hba (hP b)) (hP a)
  · exact hντ
  · simpa only [affinePoint_zero] using hdet

end

end PanelMoments.SourceMixedPairDeterminant

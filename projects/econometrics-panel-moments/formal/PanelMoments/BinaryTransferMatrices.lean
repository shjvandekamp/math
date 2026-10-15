import PanelMoments.BinaryTransferRank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases

set_option autoImplicit false

/-!
# Actual binary transition products and the normalized transfer words

The two rows of `oddsMatrix` have odds `c*z` and `ρ*c*z`. The ordered
matrix product has off-diagonal entries `q` and `r`; division of `q` and
`z*r` by its determinant gives exactly the existing ordered `Q/R` prefix
sums. The determinant factor is unchanged when a list position moves to
the front, so this normalization also matches the actual moved-word family.

All divisions are justified by explicit assumptions at the evaluation point.
These are algebraic identities, not a rank transfer on a function space or
a statement about polar limits of the three-state source model.
-/

namespace PanelMoments.BinaryTransferMatrices

open BinaryTransferAlgebra

noncomputable section

variable {K : Type*} [Field K]

/-- The actual two-state transition matrix in row-odds coordinates. -/
def oddsMatrix (ρ c z : K) : Matrix (Fin 2) (Fin 2) K :=
  !![1 / (1 + c * z), c * z / (1 + c * z);
    1 / (1 + ρ * c * z), ρ * c * z / (1 + ρ * c * z)]

def determinantFactor (ρ c z : K) : K :=
  (ρ - 1) * c * z / ((1 + c * z) * (1 + ρ * c * z))

/-- The same list order is used for the transition matrices and scalar factors. -/
def orderedProduct (ρ : K) (cs : List K) (z : K) : Matrix (Fin 2) (Fin 2) K :=
  (cs.map (fun c => oddsMatrix ρ c z)).prod

def determinantProduct (ρ : K) (cs : List K) (z : K) : K :=
  (cs.map (fun c => determinantFactor ρ c z)).prod

/-- Nonzero odds coefficients and the two excluded row-denominator poles. -/
def RegularAt (ρ : K) (cs : List K) (z : K) : Prop :=
  ∀ c ∈ cs, c ≠ 0 ∧ 1 + c * z ≠ 0 ∧ 1 + ρ * c * z ≠ 0

def RowSumOne (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  ∀ i, M i 0 + M i 1 = 1

theorem oddsMatrix_rows (ρ c z : K) (h₀ : 1 + c * z ≠ 0)
    (h₁ : 1 + ρ * c * z ≠ 0) : RowSumOne (oddsMatrix ρ c z) := by
  intro i
  fin_cases i
  · change 1 / (1 + c * z) + c * z / (1 + c * z) = 1
    field_simp [h₀]
  · change 1 / (1 + ρ * c * z) + ρ * c * z / (1 + ρ * c * z) = 1
    field_simp [h₁]

theorem rowSumOne_mul {M P : Matrix (Fin 2) (Fin 2) K}
    (hM : RowSumOne M) (hP : RowSumOne P) : RowSumOne (M * P) := by
  intro i
  calc
    (M * P) i 0 + (M * P) i 1 =
        M i 0 * (P 0 0 + P 0 1) + M i 1 * (P 1 0 + P 1 1) := by
      simp only [Matrix.mul_apply, Fin.sum_univ_two]
      ring
    _ = 1 := by rw [hP 0, hP 1, mul_one, mul_one, hM i]

theorem det_eq_one_sub {M : Matrix (Fin 2) (Fin 2) K} (hM : RowSumOne M) :
    M.det = 1 - M 0 1 - M 1 0 := by
  have h₀ : M 0 0 = 1 - M 0 1 := eq_sub_of_add_eq (hM 0)
  have h₁ : M 1 1 = 1 - M 1 0 := eq_sub_of_add_eq (by simpa [add_comm] using hM 1)
  rw [Matrix.det_fin_two, h₀, h₁]
  ring

theorem product_q {M P : Matrix (Fin 2) (Fin 2) K}
    (hM : RowSumOne M) (hP : RowSumOne P) :
    (M * P) 0 1 = P 0 1 + P.det * M 0 1 := by
  have h₀ : M 0 0 = 1 - M 0 1 := eq_sub_of_add_eq (hM 0)
  have h₁ : P 1 1 = 1 - P 1 0 := eq_sub_of_add_eq (by simpa [add_comm] using hP 1)
  rw [(Matrix.two_mul_expl M P).2.1, h₀, h₁, det_eq_one_sub hP]
  ring

theorem product_r {M P : Matrix (Fin 2) (Fin 2) K}
    (hM : RowSumOne M) (hP : RowSumOne P) :
    (M * P) 1 0 = P 1 0 + P.det * M 1 0 := by
  have h₀ : P 0 0 = 1 - P 0 1 := eq_sub_of_add_eq (hP 0)
  have h₁ : M 1 1 = 1 - M 1 0 := eq_sub_of_add_eq (by simpa [add_comm] using hM 1)
  rw [(Matrix.two_mul_expl M P).2.2.1, h₀, h₁, det_eq_one_sub hP]
  ring

theorem oddsMatrix_det (ρ c z : K) :
    (oddsMatrix ρ c z).det = determinantFactor ρ c z := by
  rw [Matrix.det_fin_two]
  change 1 / (1 + c * z) * (ρ * c * z / (1 + ρ * c * z)) -
    c * z / (1 + c * z) * (1 / (1 + ρ * c * z)) = _
  unfold determinantFactor
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem determinantFactor_ne_zero (ρ c z : K) (hρ : ρ ≠ 1) (hc : c ≠ 0)
    (hz : z ≠ 0) (h₀ : 1 + c * z ≠ 0) (h₁ : 1 + ρ * c * z ≠ 0) :
    determinantFactor ρ c z ≠ 0 :=
  div_ne_zero (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hρ) hc) hz) (mul_ne_zero h₀ h₁)

theorem determinantFactor_mul_H (ρ c z : K) (hρ : ρ ≠ 1) (hc : c ≠ 0)
    (hz : z ≠ 0) (h₀ : 1 + c * z ≠ 0) (h₁ : 1 + ρ * c * z ≠ 0) :
    determinantFactor ρ c z * H ρ c z = 1 := by
  unfold determinantFactor H
  field_simp [sub_ne_zero.mpr hρ, hc, hz, h₀, h₁]

theorem determinantFactor_mul_Q (ρ c z : K) (hρ : ρ ≠ 1)
    (h₀ : 1 + c * z ≠ 0) (h₁ : 1 + ρ * c * z ≠ 0) :
    determinantFactor ρ c z * Q ρ c z = (oddsMatrix ρ c z) 0 1 := by
  change determinantFactor ρ c z * Q ρ c z = c * z / (1 + c * z)
  unfold determinantFactor Q
  field_simp [sub_ne_zero.mpr hρ, h₀, h₁]

theorem determinantFactor_mul_R (ρ c z : K) (hρ : ρ ≠ 1) (hc : c ≠ 0)
    (h₀ : 1 + c * z ≠ 0) (h₁ : 1 + ρ * c * z ≠ 0) :
    determinantFactor ρ c z * R ρ c z = z * (oddsMatrix ρ c z) 1 0 := by
  change determinantFactor ρ c z * R ρ c z = z * (1 / (1 + ρ * c * z))
  unfold determinantFactor R
  field_simp [sub_ne_zero.mpr hρ, hc, h₀, h₁]

theorem orderedProduct_rows (ρ : K) (cs : List K) (z : K)
    (hcs : RegularAt ρ cs z) : RowSumOne (orderedProduct ρ cs z) := by
  induction cs with
  | nil =>
      intro i
      fin_cases i <;> simp [orderedProduct]
  | cons c cs ih =>
      have hc := hcs c (by simp)
      have ht : RegularAt ρ cs z := fun d hd => hcs d (by simp [hd])
      change RowSumOne (oddsMatrix ρ c z * orderedProduct ρ cs z)
      exact rowSumOne_mul (oddsMatrix_rows ρ c z hc.2.1 hc.2.2) (ih ht)

theorem orderedProduct_det (ρ : K) (cs : List K) (z : K) :
    (orderedProduct ρ cs z).det = determinantProduct ρ cs z := by
  induction cs with
  | nil => simp [orderedProduct, determinantProduct]
  | cons c cs ih =>
      change (oddsMatrix ρ c z * orderedProduct ρ cs z).det =
        determinantFactor ρ c z * determinantProduct ρ cs z
      rw [Matrix.det_mul, oddsMatrix_det ρ c z, ih]

theorem determinantProduct_ne_zero (ρ : K) (cs : List K) (z : K)
    (hρ : ρ ≠ 1) (hz : z ≠ 0) (hcs : RegularAt ρ cs z) :
    determinantProduct ρ cs z ≠ 0 := by
  induction cs with
  | nil => simp [determinantProduct]
  | cons c cs ih =>
      have hc := hcs c (by simp)
      have ht : RegularAt ρ cs z := fun d hd => hcs d (by simp [hd])
      exact mul_ne_zero (determinantFactor_ne_zero ρ c z hρ hc.1 hz hc.2.1 hc.2.2) (ih ht)

/-- Both off-diagonal numerators are the actual existing ordered prefix sums. -/
theorem orderedProduct_entries (ρ : K) (cs : List K) (z : K)
    (hρ : ρ ≠ 1) (hz : z ≠ 0) (hcs : RegularAt ρ cs z) :
    (orderedProduct ρ cs z) 0 1 = determinantProduct ρ cs z * prefixQ ρ cs z ∧
      z * (orderedProduct ρ cs z) 1 0 = determinantProduct ρ cs z * prefixR ρ cs z := by
  induction cs with
  | nil => simp [orderedProduct, determinantProduct]
  | cons c cs ih =>
      have hc := hcs c (by simp)
      have ht : RegularAt ρ cs z := fun d hd => hcs d (by simp [hd])
      have hi := ih ht
      have hd := orderedProduct_det ρ cs z
      have hrows := oddsMatrix_rows ρ c z hc.2.1 hc.2.2
      have htrows := orderedProduct_rows ρ cs z ht
      have hH := determinantFactor_mul_H ρ c z hρ hc.1 hz hc.2.1 hc.2.2
      have hQ := determinantFactor_mul_Q ρ c z hρ hc.2.1 hc.2.2
      have hR := determinantFactor_mul_R ρ c z hρ hc.1 hc.2.1 hc.2.2
      constructor
      · change (oddsMatrix ρ c z * orderedProduct ρ cs z) 0 1 =
          (determinantFactor ρ c z * determinantProduct ρ cs z) *
            (Q ρ c z + H ρ c z * prefixQ ρ cs z)
        rw [product_q hrows htrows, hd, hi.1, ← hQ]
        calc
          _ = determinantProduct ρ cs z * (determinantFactor ρ c z * Q ρ c z) +
              determinantProduct ρ cs z * (determinantFactor ρ c z * H ρ c z) *
                prefixQ ρ cs z := by rw [hH]; ring
          _ = _ := by ring
      · change z * (oddsMatrix ρ c z * orderedProduct ρ cs z) 1 0 =
          (determinantFactor ρ c z * determinantProduct ρ cs z) *
            (R ρ c z + H ρ c z * prefixR ρ cs z)
        rw [product_r hrows htrows, hd]
        calc
          _ = z * (orderedProduct ρ cs z) 1 0 +
              determinantProduct ρ cs z * (z * (oddsMatrix ρ c z) 1 0) := by ring
          _ = determinantProduct ρ cs z * prefixR ρ cs z +
              determinantProduct ρ cs z * (determinantFactor ρ c z * R ρ c z) := by
            rw [hi.2, ← hR]
          _ = determinantProduct ρ cs z * (determinantFactor ρ c z * R ρ c z) +
              determinantProduct ρ cs z * (determinantFactor ρ c z * H ρ c z) *
                prefixR ρ cs z := by rw [hH]; ring
          _ = _ := by ring

theorem orderedProduct_q_normalized (ρ : K) (cs : List K) (z : K)
    (hρ : ρ ≠ 1) (hz : z ≠ 0) (hcs : RegularAt ρ cs z) :
    (orderedProduct ρ cs z) 0 1 / determinantProduct ρ cs z = prefixQ ρ cs z := by
  rw [(orderedProduct_entries ρ cs z hρ hz hcs).1]
  exact mul_div_cancel_left₀ _ (determinantProduct_ne_zero ρ cs z hρ hz hcs)

theorem orderedProduct_r_normalized (ρ : K) (cs : List K) (z : K)
    (hρ : ρ ≠ 1) (hz : z ≠ 0) (hcs : RegularAt ρ cs z) :
    (z * (orderedProduct ρ cs z) 1 0) / determinantProduct ρ cs z = prefixR ρ cs z := by
  rw [(orderedProduct_entries ρ cs z hρ hz hcs).2]
  exact mul_div_cancel_left₀ _ (determinantProduct_ne_zero ρ cs z hρ hz hcs)

/-- Moving a position to the front preserves the common determinant factor. -/
theorem determinantProduct_movedWord (ρ : ℝ) (cs : List ℝ) (i : Fin cs.length) (z : ℝ) :
    determinantProduct ρ (BinaryTransferRank.movedWord cs i) z = determinantProduct ρ cs z := by
  have hsplit : (cs.take i.val ++ [cs[i.val]]) ++ cs.drop (i.val + 1) = cs := by
    rw [List.take_append_getElem i.isLt, List.take_append_drop]
  calc
    _ = determinantProduct ρ ((cs.take i.val ++ [cs[i.val]]) ++ cs.drop (i.val + 1)) z := by
      simp only [determinantProduct, BinaryTransferRank.movedWord, List.map_cons,
        List.map_append, List.map_nil, List.prod_cons, List.prod_append, List.prod_nil]
      ring
    _ = _ := congrArg (fun ds => determinantProduct ρ ds z) hsplit

theorem regularAt_movedWord (ρ : ℝ) (cs : List ℝ) (i : Fin cs.length) (z : ℝ)
    (hcs : RegularAt ρ cs z) : RegularAt ρ (BinaryTransferRank.movedWord cs i) z := by
  intro c hc
  simp only [BinaryTransferRank.movedWord, List.mem_cons, List.mem_append] at hc
  rcases hc with rfl | hc | hc
  · exact hcs _ (List.getElem_mem i.isLt)
  · exact hcs _ (List.mem_of_mem_take hc)
  · exact hcs _ (List.mem_of_mem_drop hc)

/-- The normalized upper off-diagonal entry of each actual moved product is
exactly the existing `wordQ` function at every regular nonzero point. -/
theorem movedWord_q_normalized (ρ : ℝ) (cs : List ℝ) (i : Fin cs.length)
    (z : BinaryTransferSpan.NonzeroReal) (hρ : ρ ≠ 1) (hcs : RegularAt ρ cs z.val) :
    (orderedProduct ρ (BinaryTransferRank.movedWord cs i) z.val) 0 1 /
        determinantProduct ρ cs z.val = BinaryTransferRank.wordQ ρ cs i z := by
  rw [← determinantProduct_movedWord ρ cs i z.val]
  exact orderedProduct_q_normalized ρ _ z.val hρ z.property
    (regularAt_movedWord ρ cs i z.val hcs)

/-- The lower off-diagonal entry includes the required factor `z`. -/
theorem movedWord_r_normalized (ρ : ℝ) (cs : List ℝ) (i : Fin cs.length)
    (z : BinaryTransferSpan.NonzeroReal) (hρ : ρ ≠ 1) (hcs : RegularAt ρ cs z.val) :
    (z.val * (orderedProduct ρ (BinaryTransferRank.movedWord cs i) z.val) 1 0) /
        determinantProduct ρ cs z.val = BinaryTransferRank.wordR ρ cs i z := by
  rw [← determinantProduct_movedWord ρ cs i z.val]
  exact orderedProduct_r_normalized ρ _ z.val hρ z.property
    (regularAt_movedWord ρ cs i z.val hcs)

end

end PanelMoments.BinaryTransferMatrices

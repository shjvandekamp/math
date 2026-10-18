import PanelMoments.BinaryTransferMatrices
import Mathlib.Order.Interval.Set.Infinite

set_option autoImplicit false

/-!
# Rank parity for actual binary matrix products on the positive domain

Restriction from nonzero to positive real arguments is injective on every
polynomial-cleared function space. The existing word span lies in such a
space, by the paired-defect clearing bounds and the affine baseline remainder.
For positive odds parameters, all transition denominators are nonzero on this
domain. Multiplication by the common nonzero determinant product then sends
the restricted word columns to the actual matrix-product columns.

The resulting rank is over constant real scalars and concerns the auxiliary
binary products. It does not assert independence of the original three-state
source family or any polar perturbation theorem.
-/

namespace PanelMoments.BinaryTransferPositiveRank

open Polynomial BinaryTransferIndependence BinaryTransferMatrices
open BinaryTransferRank

noncomputable section

abbrev PositiveReal := {z : ℝ // 0 < z}
abbrev PositiveSpace := PositiveReal → ℝ

/-- Restrict the existing functions to positive arguments. -/
def restrictPositive : BinaryTransferSpan.FunctionSpace →ₗ[ℝ] PositiveSpace where
  toFun f z := f ⟨z.val, ne_of_gt z.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A polynomial is determined by its evaluations on the positive half-line. -/
theorem positive_evaluation_injective : Function.Injective
    (fun p : ℝ[X] => (fun z : PositiveReal => p.eval z.val)) := by
  intro p q h
  apply Polynomial.eq_of_infinite_eval_eq
  exact (Set.Ioi_infinite (0 : ℝ)).mono (fun z hz => congrFun h ⟨z, hz⟩)

/-- No polynomial-cleared function is lost by restricting to positive arguments. -/
theorem restrictPositive_clearedSpace_injective (k d : ℕ) :
    Function.Injective (restrictPositive.domRestrict (clearedSpace k d)) := by
  intro f g h
  obtain ⟨p, _hp, hpf⟩ := f.property
  obtain ⟨q, _hq, hqg⟩ := g.property
  have hpq : p = q := by
    apply positive_evaluation_injective
    funext z
    change p.eval z.val = q.eval z.val
    rw [hpf ⟨z.val, ne_of_gt z.property⟩, hqg ⟨z.val, ne_of_gt z.property⟩]
    exact congrArg (fun x : ℝ => z.val ^ k * x) (congrFun h z)
  apply Subtype.ext
  funext z
  apply mul_left_cancel₀ (pow_ne_zero k z.property)
  rw [← hpf z, ← hqg z, hpq]

theorem blockColumn_mem_clearedSpace (ρ c : ℝ) (k : ℕ) (b : Bool)
    (hρ : ρ ≠ 1) (hc : c ≠ 0) :
    blockColumn ρ c b ∈ clearedSpace k (2 * k + 1) := by
  cases b with
  | false =>
      have h := affine_mem_clearedSpace k
        ((0 * c + 1) / ((ρ - 1) * c)) ((0 * ρ * c + 1) / (ρ - 1))
      rw [← block_combination_eq_affine ρ c 0 1 hρ hc] at h
      simpa [blockColumn] using h
  | true =>
      have h := affine_mem_clearedSpace k
        ((1 * c + 0) / ((ρ - 1) * c)) ((1 * ρ * c + 0) / (ρ - 1))
      rw [← block_combination_eq_affine ρ c 1 0 hρ hc] at h
      simpa [blockColumn] using h

/-- The complete word span has a common polynomial-clearing bound. The
baseline remainder is affine and the other terms lie in the paired span. -/
theorem wordSpan_le_clearedSpace (ρ : ℝ) (cs : List ℝ) (hne : cs ≠ [])
    (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, c ≠ 0)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) :
    wordSpan ρ cs ≤ clearedSpace cs.length (2 * cs.length + 1) := by
  induction cs using List.reverseRecOn with
  | nil => exact False.elim (hne rfl)
  | append_singleton cs c _ih =>
      have hc : c ≠ 0 := hcs c (by simp)
      have ht : ∀ d ∈ cs, d ≠ 0 := fun d hd => hcs d (by simp [hd])
      let k := (cs ++ [c]).length
      have hpaired : BinaryTransferSpan.pairedSpan ρ (cs ++ [c]) ≤
          clearedSpace k (2 * k + 1) :=
        pairedSpan_le_clearedSpace ρ (cs ++ [c]) k (by dsimp [k]; omega) hρ hcs
      rw [wordSpan_eq_paired_sup_baseline ρ (cs ++ [c]) (by simp) hρ hcs]
      refine sup_le hpaired ?_
      apply Submodule.span_le.mpr
      rintro _ ⟨b, rfl⟩
      have hrem : baselineColumn ρ (cs ++ [c]) b -
          (((cs.length + 1) % 2 : ℕ) : ℝ) • blockColumn ρ c b ∈
          BinaryTransferSpan.pairedSpan ρ (cs ++ [c]) := by
        cases b with
        | false =>
            simpa [baselineColumn, blockColumn] using
              BinaryTransferSpan.baselineR_sub_parity_mem ρ c cs hρ ht hc hadj
        | true =>
            simpa [baselineColumn, blockColumn] using
              BinaryTransferSpan.baselineQ_sub_parity_mem ρ c cs hρ ht hc hadj
      have h := (clearedSpace k (2 * k + 1)).add_mem (hpaired hrem)
        ((clearedSpace k (2 * k + 1)).smul_mem (((cs.length + 1) % 2 : ℕ) : ℝ)
          (blockColumn_mem_clearedSpace ρ c k b hρ hc))
      simpa only [sub_add_cancel, k, SetLike.mem_coe] using h

theorem restrictPositive_wordSpan_injective (ρ : ℝ) (cs : List ℝ) (hne : cs ≠ [])
    (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, c ≠ 0)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) :
    Function.Injective (restrictPositive.domRestrict (wordSpan ρ cs)) := by
  intro f g h
  have hclear := wordSpan_le_clearedSpace ρ cs hne hρ hcs hadj
  have heq :
      (⟨f.val, hclear f.property⟩ : clearedSpace cs.length (2 * cs.length + 1)) =
        ⟨g.val, hclear g.property⟩ :=
    restrictPositive_clearedSpace_injective cs.length (2 * cs.length + 1) h
  apply Subtype.ext
  exact congrArg (fun x : clearedSpace cs.length (2 * cs.length + 1) => x.val) heq

/-- Positive parameters avoid every excluded transition pole on this domain. -/
theorem regularAt_positive (ρ : ℝ) (cs : List ℝ) (z : PositiveReal)
    (hρ : 0 < ρ) (hcs : ∀ c ∈ cs, 0 < c) : RegularAt ρ cs z.val := by
  intro c hc
  refine ⟨ne_of_gt (hcs c hc), ne_of_gt ?_, ne_of_gt ?_⟩
  · exact add_pos zero_lt_one (mul_pos (hcs c hc) z.property)
  · exact add_pos zero_lt_one (mul_pos (mul_pos hρ (hcs c hc)) z.property)

def determinantScale (ρ : ℝ) (cs : List ℝ) : PositiveSpace →ₗ[ℝ] PositiveSpace where
  toFun f z := determinantProduct ρ cs z.val * f z
  map_add' f g := by
    funext z
    exact mul_add _ _ _
  map_smul' a f := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem determinantScale_injective (ρ : ℝ) (cs : List ℝ)
    (hρpos : 0 < ρ) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, 0 < c) :
    Function.Injective (determinantScale ρ cs) := by
  intro f g h
  funext z
  exact mul_left_cancel₀
    (determinantProduct_ne_zero ρ cs z.val hρ (ne_of_gt z.property)
      (regularAt_positive ρ cs z hρpos hcs)) (congrFun h z)

/-- The common linear map which realizes the matrix-product columns. -/
def transferMap (ρ : ℝ) (cs : List ℝ) :
    BinaryTransferSpan.FunctionSpace →ₗ[ℝ] PositiveSpace :=
  (determinantScale ρ cs).comp restrictPositive

theorem transferMap_wordSpan_injective (ρ : ℝ) (cs : List ℝ) (hne : cs ≠ [])
    (hρpos : 0 < ρ) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, 0 < c)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) :
    Function.Injective ((transferMap ρ cs).domRestrict (wordSpan ρ cs)) :=
  (determinantScale_injective ρ cs hρpos hρ hcs).comp
    (restrictPositive_wordSpan_injective ρ cs hne hρ
      (fun c hc => ne_of_gt (hcs c hc)) hadj)

/-- `true` selects the upper off-diagonal entry `q`; `false` selects `z*r`. -/
def matrixColumn (ρ : ℝ) (cs : List ℝ) (i : Fin cs.length × Bool) : PositiveSpace :=
  fun z => if i.2 then (orderedProduct ρ (movedWord cs i.1) z.val) 0 1
    else z.val * (orderedProduct ρ (movedWord cs i.1) z.val) 1 0

def matrixSpan (ρ : ℝ) (cs : List ℝ) : Submodule ℝ PositiveSpace :=
  Submodule.span ℝ (Set.range (matrixColumn ρ cs))

/-- Exact equality with the actual ordered matrix products, not a surrogate
family having only the same formal column count. -/
theorem matrixColumn_eq_transferMap (ρ : ℝ) (cs : List ℝ)
    (hρpos : 0 < ρ) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, 0 < c)
    (i : Fin cs.length × Bool) :
    matrixColumn ρ cs i = transferMap ρ cs (wordColumn ρ cs i) := by
  funext z
  have hreg := regularAt_movedWord ρ cs i.1 z.val (regularAt_positive ρ cs z hρpos hcs)
  have hentries := orderedProduct_entries ρ (movedWord cs i.1) z.val hρ
    (ne_of_gt z.property) hreg
  rw [determinantProduct_movedWord] at hentries
  rcases i with ⟨i, b⟩
  cases b with
  | false => exact hentries.2
  | true => exact hentries.1

theorem matrixSpan_eq_range (ρ : ℝ) (cs : List ℝ)
    (hρpos : 0 < ρ) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, 0 < c) :
    matrixSpan ρ cs = LinearMap.range ((transferMap ρ cs).domRestrict (wordSpan ρ cs)) := by
  rw [LinearMap.range_domRestrict, wordSpan, Submodule.map_span, ← Set.range_comp]
  have hcolumns : matrixColumn ρ cs = transferMap ρ cs ∘ wordColumn ρ cs :=
    funext (matrixColumn_eq_transferMap ρ cs hρpos hρ hcs)
  rw [matrixSpan, hcolumns]

/-- Positive restriction and common determinant multiplication preserve the
dimension of the existing normalized word span. -/
theorem finrank_matrixSpan_eq_wordSpan (ρ : ℝ) (cs : List ℝ) (hne : cs ≠ [])
    (hρpos : 0 < ρ) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, 0 < c)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) :
    Module.finrank ℝ (matrixSpan ρ cs) = Module.finrank ℝ (wordSpan ρ cs) := by
  rw [matrixSpan_eq_range ρ cs hρpos hρ hcs]
  exact LinearMap.finrank_range_of_inj
    (transferMap_wordSpan_injective ρ cs hne hρpos hρ hcs hadj)

/-- Rank parity for the actual moved binary products as functions on `z > 0`,
over constant real coefficients. -/
theorem finrank_matrixSpan_parity (ρ : ℝ) (cs : List ℝ) (hne : cs ≠ [])
    (hρpos : 0 < ρ) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, 0 < c)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) :
    Module.finrank ℝ (matrixSpan ρ cs) =
      if cs.length % 2 = 1 then 2 * cs.length else 2 * cs.length - 2 := by
  rw [finrank_matrixSpan_eq_wordSpan ρ cs hne hρpos hρ hcs hadj]
  exact finrank_wordSpan_parity ρ cs hne (ne_of_gt hρpos) hρ
    (fun c hc => ne_of_gt (hcs c hc)) hadj

theorem finrank_matrixSpan_odd (ρ : ℝ) (cs : List ℝ) (hne : cs ≠ [])
    (hρpos : 0 < ρ) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, 0 < c)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) (hodd : cs.length % 2 = 1) :
    Module.finrank ℝ (matrixSpan ρ cs) = 2 * cs.length := by
  rw [finrank_matrixSpan_parity ρ cs hne hρpos hρ hcs hadj, ite_eq_left hodd]

theorem finrank_matrixSpan_even (ρ : ℝ) (cs : List ℝ) (hne : cs ≠ [])
    (hρpos : 0 < ρ) (hρ : ρ ≠ 1) (hcs : ∀ c ∈ cs, 0 < c)
    (hadj : cs.IsChain (fun x y : ℝ => x ≠ y)) (heven : cs.length % 2 = 0) :
    Module.finrank ℝ (matrixSpan ρ cs) = 2 * cs.length - 2 := by
  rw [finrank_matrixSpan_parity ρ cs hne hρpos hρ hcs hadj, ite_eq_right (by omega)]

end

end PanelMoments.BinaryTransferPositiveRank

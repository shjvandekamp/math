import PanelMoments.Polynomial
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Lean.Elab.Tactic.Omega

/-!
The finite linear-algebra step used to integrate explicit moment and restriction
minors. The main model application must prove each minor is nonzero on an
explicitly constructed, nonempty generic region; this file assumes no ranks.
-/

namespace PanelMoments

open scoped BigOperators

noncomputable section

def momentSubmodule {Q : ℕ} (A : Table Q) (T : ℕ) (r : State Q) :
    Submodule ℝ (Path Q T → ℝ) where
  carrier := {m | IsMoment A T r m}
  zero_mem' := by intro η hη; simp
  add_mem' := by
    intro m n hm hn η hη
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hm η hη, hn η hη, add_zero]
  smul_mem' := by
    intro c m hm η hη
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
    rw [hm η hη, mul_zero]

@[simp] theorem mem_momentSubmodule {Q : ℕ} (A : Table Q) (T : ℕ)
    (r : State Q) (m : Path Q T → ℝ) :
    m ∈ momentSubmodule A T r ↔ IsMoment A T r m := Iff.rfl

theorem finite_basis_certificate {P : Type*} [Fintype P] [DecidableEq P]
    (hP : Fintype.card P = 81)
    (v : Fin 33 → P → ℝ) (ev : Fin 33 → P)
    (C : Matrix (Fin 48) P ℝ) (cols : Fin 48 → P)
    (S : Submodule ℝ (P → ℝ))
    (hvS : ∀ i, v i ∈ S) (hSK : S ≤ LinearMap.ker C.mulVecLin)
    (hdetV : Matrix.det (fun i j => v i (ev j)) ≠ 0)
    (hdetC : (C.submatrix id cols).det ≠ 0) :
    LinearIndependent ℝ v ∧ S = Submodule.span ℝ (Set.range v) ∧
      Module.finrank ℝ S = 33 := by
  classical
  let E : (P → ℝ) →ₗ[ℝ] (Fin 33 → ℝ) :=
    { toFun := fun f j => f (ev j)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hli : LinearIndependent ℝ v := by
    apply LinearIndependent.of_comp E
    change LinearIndependent ℝ (fun i j => v i (ev j))
    exact Matrix.linearIndependent_rows_of_det_ne_zero hdetV
  let B := Submodule.span ℝ (Set.range v)
  have hB : Module.finrank ℝ B = 33 := by
    simpa [B] using finrank_span_eq_card hli
  have hBS : B ≤ S := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hvS i
  have hMinor : (C.submatrix id cols).rank = 48 := by
    simpa using Matrix.rank_of_det_ne_zero hdetC
  have hRank : C.rank = 48 := by
    apply le_antisymm
    · simpa using Matrix.rank_le_card_height C
    · have h := Matrix.rank_submatrix_le C id cols
      simpa [hMinor] using h
  have hDimV : Module.finrank ℝ (P → ℝ) = 81 := by
    simpa [hP] using (Module.finrank_fintype_fun_eq_card ℝ :
      Module.finrank ℝ (P → ℝ) = Fintype.card P)
  have hKer : Module.finrank ℝ (LinearMap.ker C.mulVecLin) = 33 := by
    have h := LinearMap.finrank_range_add_finrank_ker C.mulVecLin
    change C.rank + Module.finrank ℝ (LinearMap.ker C.mulVecLin) =
      Module.finrank ℝ (P → ℝ) at h
    omega
  have hDimS : Module.finrank ℝ S = 33 := by
    have hlo := Submodule.finrank_mono hBS
    have hhi := Submodule.finrank_mono hSK
    omega
  have hEq : B = S :=
    Submodule.eq_of_le_of_finrank_eq hBS (hB.trans hDimS.symm)
  exact ⟨hli, hEq.symm, hDimS⟩

end

end PanelMoments

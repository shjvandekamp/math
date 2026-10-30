import PanelMoments.EconomicFamily
import PanelMoments.GeneralConicWitness
import PanelMoments.GeneralGeometry

/-!
# An explicit generic economic region for the structural geometry

The defining analytic function is a fixed finite product of separator values,
cross-block line evaluations, and within-block coefficient differences. Its
definition contains no rank, span, or dimension predicate. The economic witness
makes every factor nonzero, and hence the region is nonempty, open, and dense.
-/

namespace PanelMoments.StructuralGenericity

open scoped BigOperators
open MvPolynomial GeneralGeometry

noncomputable section

abbrev Blocks (T : ℕ) := Fin (T - 1)
abbrev Parameter (T : ℕ) := EconomicFamily.EconomicParameter T

def blockA {T : ℕ} (θ : Parameter T) (t : Blocks T) (r : Fin 3) : ℝ :=
  EconomicFamily.parameterTable θ (t.val + 1) r 1

def blockB {T : ℕ} (θ : Parameter T) (t : Blocks T) (r : Fin 3) : ℝ :=
  EconomicFamily.parameterTable θ (t.val + 1) r 2

def coefficientVectors {T : ℕ} (θ : Parameter T) (t : Blocks T) : Fin 3 → Point :=
  CubicIdeal.coefficientVectors (blockA θ t) (blockB θ t)

def localFactor {T : ℕ} (θ : Parameter T) : ℝ :=
  ∏ t : Blocks T, ∏ i : Fin 6,
    eval (sixPoints (coefficientVectors θ t) i) (separator (coefficientVectors θ t) i)

def crossFactor {T : ℕ} (θ : Parameter T) : ℝ :=
  ∏ t : Blocks T, ∏ s ∈ Finset.univ.erase t, ∏ i : Fin 6, ∏ r : Fin 3,
    eval (sixPoints (coefficientVectors θ t) i) (linearForm (coefficientVectors θ s r))

def differenceFactor {T : ℕ} (θ : Parameter T) : ℝ :=
  ∏ t : Blocks T, ∏ r : Fin 3, ∏ s ∈ Finset.univ.erase r,
    (blockA θ t r - blockA θ t s)

/-- A fixed analytic expression in the economic parameters. -/
def exceptionalProduct {T : ℕ} (θ : Parameter T) : ℝ :=
  localFactor θ * crossFactor θ * differenceFactor θ

def genericRegion (T : ℕ) : Set (Parameter T) := {θ | exceptionalProduct θ ≠ 0}

theorem blockA_pos {T : ℕ} (θ : Parameter T) (t : Blocks T) (r : Fin 3) :
    0 < blockA θ t r :=
  EconomicFamily.parameterTable_positive θ (t.val + 1) r 1

theorem blockA_analytic (T : ℕ) (t : Blocks T) (r : Fin 3) :
    AnalyticOnNhd ℝ (fun θ : Parameter T => blockA θ t r) Set.univ :=
  EconomicFamily.parameterTable_analytic T (t.val + 1) r 1

theorem blockB_analytic (T : ℕ) (t : Blocks T) (r : Fin 3) :
    AnalyticOnNhd ℝ (fun θ : Parameter T => blockB θ t r) Set.univ :=
  EconomicFamily.parameterTable_analytic T (t.val + 1) r 2

theorem coefficientVectors_analyticAt {T : ℕ} (θ : Parameter T)
    (t : Blocks T) (r j : Fin 3) :
    AnalyticAt ℝ (fun z : Parameter T => coefficientVectors z t r j) θ := by
  fin_cases j
  · exact analyticAt_const
  · exact blockA_analytic T t r θ (Set.mem_univ θ)
  · exact blockB_analytic T t r θ (Set.mem_univ θ)

private theorem analyticAt_cross {N : ℕ} {v w : (Fin N → ℝ) → Point}
    {x : Fin N → ℝ} (hv : ∀ j, AnalyticAt ℝ (fun z => v z j) x)
    (hw : ∀ j, AnalyticAt ℝ (fun z => w z j) x) (i : Fin 3) :
    AnalyticAt ℝ (fun z => cross (v z) (w z) i) x := by
  fin_cases i
  · simpa only [cross, Matrix.cons_val_zero', Matrix.cons_val_succ', Pi.mul_def, Pi.sub_def] using
      ((hv 1).mul (hw 2)).sub ((hv 2).mul (hw 1))
  · simpa only [cross, Matrix.cons_val_zero', Matrix.cons_val_succ', Pi.mul_def, Pi.sub_def] using
      ((hv 2).mul (hw 0)).sub ((hv 0).mul (hw 2))
  · simpa only [cross, Matrix.cons_val_zero', Matrix.cons_val_succ', Pi.mul_def, Pi.sub_def] using
      ((hv 0).mul (hw 1)).sub ((hv 1).mul (hw 0))

private theorem analyticAt_eval_linearForm {N : ℕ} {v p : (Fin N → ℝ) → Point}
    {x : Fin N → ℝ} (hv : ∀ j, AnalyticAt ℝ (fun z => v z j) x)
    (hp : ∀ j, AnalyticAt ℝ (fun z => p z j) x) :
    AnalyticAt ℝ (fun z => eval (p z) (linearForm (v z))) x := by
  simpa only [linearForm, map_add, map_mul, eval_C, eval_X, Pi.mul_def, Pi.add_def] using
    (((hv 0).mul (hp 0)).add ((hv 1).mul (hp 1))).add ((hv 2).mul (hp 2))

private theorem analyticAt_coordinatePoint {N : ℕ}
    {l : (Fin N → ℝ) → Fin 3 → Point} {x : Fin N → ℝ}
    (hl : ∀ r j, AnalyticAt ℝ (fun z => l z r j) x) (r j : Fin 3) :
    AnalyticAt ℝ (fun z => coordinatePoint (l z) r j) x :=
  analyticAt_cross (w := fun _ => coordinateVector r) (hl r) (fun _ => analyticAt_const) j

private theorem analyticAt_sixPoints {N : ℕ}
    {l : (Fin N → ℝ) → Fin 3 → Point} {x : Fin N → ℝ}
    (hl : ∀ r j, AnalyticAt ℝ (fun z => l z r j) x) (i : Fin 6) (j : Fin 3) :
    AnalyticAt ℝ (fun z => sixPoints (l z) i j) x := by
  fin_cases i
  · exact analyticAt_cross (hl 0) (hl 1) j
  · exact analyticAt_cross (hl 0) (hl 2) j
  · exact analyticAt_cross (hl 1) (hl 2) j
  · exact analyticAt_coordinatePoint hl 0 j
  · exact analyticAt_coordinatePoint hl 1 j
  · exact analyticAt_coordinatePoint hl 2 j

private theorem analyticAt_eval_separator {N : ℕ}
    {l : (Fin N → ℝ) → Fin 3 → Point} {p : (Fin N → ℝ) → Point}
    {x : Fin N → ℝ} (hl : ∀ r j, AnalyticAt ℝ (fun z => l z r j) x)
    (hp : ∀ j, AnalyticAt ℝ (fun z => p z j) x) (i : Fin 6) :
    AnalyticAt ℝ (fun z => eval (p z) (separator (l z) i)) x := by
  have hline (r : Fin 3) :
      AnalyticAt ℝ (fun z => eval (p z) (linearForm (l z r))) x :=
    analyticAt_eval_linearForm (hl r) hp
  have hconnector (r s : Fin 3) : AnalyticAt ℝ
      (fun z => eval (p z)
        (linearForm (cross (coordinatePoint (l z) r) (coordinatePoint (l z) s)))) x :=
    analyticAt_eval_linearForm
      (fun j => analyticAt_cross (analyticAt_coordinatePoint hl r)
        (analyticAt_coordinatePoint hl s) j) hp
  fin_cases i
  · simpa only [separator, Matrix.cons_val_zero', Matrix.cons_val_succ', map_mul, Pi.mul_def] using
      (hline 2).mul (hconnector 0 1)
  · simpa only [separator, Matrix.cons_val_zero', Matrix.cons_val_succ', map_mul, Pi.mul_def] using
      (hline 1).mul (hconnector 0 2)
  · simpa only [separator, Matrix.cons_val_zero', Matrix.cons_val_succ', map_mul, Pi.mul_def] using
      (hline 0).mul (hconnector 1 2)
  · simpa only [separator, Matrix.cons_val_zero', Matrix.cons_val_succ', map_mul, Pi.mul_def] using
      (hline 1).mul (hline 2)
  · simpa only [separator, Matrix.cons_val_zero', Matrix.cons_val_succ', map_mul, Pi.mul_def] using
      (hline 0).mul (hline 2)
  · simpa only [separator, Matrix.cons_val_zero', Matrix.cons_val_succ', map_mul, Pi.mul_def] using
      (hline 0).mul (hline 1)

theorem localFactor_analytic (T : ℕ) :
    AnalyticOnNhd ℝ (localFactor (T := T)) Set.univ := by
  intro θ _
  unfold localFactor
  apply Finset.analyticAt_fun_prod
  intro t _
  apply Finset.analyticAt_fun_prod
  intro i _
  exact analyticAt_eval_separator (coefficientVectors_analyticAt θ t)
    (analyticAt_sixPoints (coefficientVectors_analyticAt θ t) i) i

theorem crossFactor_analytic (T : ℕ) :
    AnalyticOnNhd ℝ (crossFactor (T := T)) Set.univ := by
  intro θ _
  unfold crossFactor
  apply Finset.analyticAt_fun_prod
  intro t _
  apply Finset.analyticAt_fun_prod
  intro s _
  apply Finset.analyticAt_fun_prod
  intro i _
  apply Finset.analyticAt_fun_prod
  intro r _
  exact analyticAt_eval_linearForm (coefficientVectors_analyticAt θ s r)
    (analyticAt_sixPoints (coefficientVectors_analyticAt θ t) i)

theorem differenceFactor_analytic (T : ℕ) :
    AnalyticOnNhd ℝ (differenceFactor (T := T)) Set.univ := by
  intro θ _
  unfold differenceFactor
  apply Finset.analyticAt_fun_prod
  intro t _
  apply Finset.analyticAt_fun_prod
  intro r _
  apply Finset.analyticAt_fun_prod
  intro s _
  exact (blockA_analytic T t r θ (Set.mem_univ θ)).sub
    (blockA_analytic T t s θ (Set.mem_univ θ))

theorem exceptionalProduct_analytic (T : ℕ) :
    AnalyticOnNhd ℝ (exceptionalProduct (T := T)) Set.univ := by
  intro θ _
  exact ((localFactor_analytic T θ (Set.mem_univ θ)).mul
    (crossFactor_analytic T θ (Set.mem_univ θ))).mul
    (differenceFactor_analytic T θ (Set.mem_univ θ))

/-- This equivalence extracts the geometric conditions from the explicit
factors. It is not the definition of the exceptional product. -/
theorem exceptionalProduct_ne_zero_iff {T : ℕ} (θ : Parameter T) :
    exceptionalProduct θ ≠ 0 ↔
      (∀ t, LocalNondegenerate (coefficientVectors θ t)) ∧
        CrossNonincident (coefficientVectors θ) ∧
          ∀ t, Function.Injective (blockA θ t) := by
  constructor
  · intro h
    have hparts : (localFactor θ * crossFactor θ) * differenceFactor θ ≠ 0 := h
    have hLC := mul_ne_zero_iff.mp hparts
    have hlocal := (mul_ne_zero_iff.mp hLC.1).1
    have hcross := (mul_ne_zero_iff.mp hLC.1).2
    have hdiff := hLC.2
    refine ⟨?_, ?_, ?_⟩
    · intro t i
      exact Finset.prod_ne_zero_iff.mp
        (Finset.prod_ne_zero_iff.mp hlocal t (Finset.mem_univ t)) i (Finset.mem_univ i)
    · intro t s hts i r
      have h₁ := Finset.prod_ne_zero_iff.mp hcross t (Finset.mem_univ t)
      have h₂ := Finset.prod_ne_zero_iff.mp h₁ s (by simp [hts.symm])
      have h₃ := Finset.prod_ne_zero_iff.mp h₂ i (Finset.mem_univ i)
      exact Finset.prod_ne_zero_iff.mp h₃ r (Finset.mem_univ r)
    · intro t r s hrs
      by_contra hne
      have h₁ := Finset.prod_ne_zero_iff.mp hdiff t (Finset.mem_univ t)
      have h₂ := Finset.prod_ne_zero_iff.mp h₁ r (Finset.mem_univ r)
      have h₃ := Finset.prod_ne_zero_iff.mp h₂ s (by simp [Ne.symm hne])
      exact h₃ (sub_eq_zero.mpr hrs)
  · rintro ⟨hlocal, hcross, hdiff⟩
    change (localFactor θ * crossFactor θ) * differenceFactor θ ≠ 0
    apply mul_ne_zero
    · apply mul_ne_zero
      · unfold localFactor
        apply Finset.prod_ne_zero_iff.mpr
        intro t _
        apply Finset.prod_ne_zero_iff.mpr
        intro i _
        exact hlocal t i
      · unfold crossFactor
        apply Finset.prod_ne_zero_iff.mpr
        intro t _
        apply Finset.prod_ne_zero_iff.mpr
        intro s hs
        apply Finset.prod_ne_zero_iff.mpr
        intro i _
        apply Finset.prod_ne_zero_iff.mpr
        intro r _
        exact hcross t s (Finset.ne_of_mem_erase hs).symm i r
    · unfold differenceFactor
      apply Finset.prod_ne_zero_iff.mpr
      intro t _
      apply Finset.prod_ne_zero_iff.mpr
      intro r _
      apply Finset.prod_ne_zero_iff.mpr
      intro s hs
      exact sub_ne_zero.mpr ((hdiff t).ne (Finset.ne_of_mem_erase hs).symm)

@[simp]
theorem blockA_witness (T : ℕ) (t : Blocks T) (r : Fin 3) :
    blockA (EconomicFamily.parameterWitness T) t r =
      EconomicFamily.structuralConicParameter t r := by
  simpa [blockA] using
    EconomicFamily.parameterWitness_structural_table T t r 1

@[simp]
theorem blockB_witness (T : ℕ) (t : Blocks T) (r : Fin 3) :
    blockB (EconomicFamily.parameterWitness T) t r =
      EconomicFamily.structuralConicParameter t r ^ 2 := by
  exact EconomicFamily.parameterWitness_structural_table T t r 2

theorem coefficientVectors_witness (T : ℕ) (t : Blocks T) :
    coefficientVectors (EconomicFamily.parameterWitness T) t =
      GeneralConicWitness.coefficients (EconomicFamily.structuralConicParameter t) := by
  funext r j
  fin_cases j <;>
    simp [coefficientVectors, GeneralConicWitness.coefficients, CubicIdeal.coefficientVectors]

theorem exceptionalProduct_witness (T : ℕ) :
    exceptionalProduct (EconomicFamily.parameterWitness T) ≠ 0 := by
  apply (exceptionalProduct_ne_zero_iff (EconomicFamily.parameterWitness T)).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro t
    rw [coefficientVectors_witness]
    exact GeneralConicWitness.localNondegenerate
      (EconomicFamily.structuralConicParameter t)
      (EconomicFamily.structuralConicParameter_pos t)
      (EconomicFamily.structuralConicParameter_row_injective t)
  · have hcoeff : coefficientVectors (EconomicFamily.parameterWitness T) =
        fun t => GeneralConicWitness.coefficients
          (EconomicFamily.structuralConicParameter t) :=
      funext (coefficientVectors_witness T)
    rw [hcoeff]
    exact GeneralConicWitness.crossNonincident
      (fun t : Blocks T => EconomicFamily.structuralConicParameter t)
      (fun t => EconomicFamily.structuralConicParameter_pos t)
      (EconomicFamily.structuralConicParameter_injective T)
  · intro t r s hrs
    apply EconomicFamily.structuralConicParameter_row_injective t
    simpa only [blockA_witness] using hrs

theorem genericRegion_nonempty (T : ℕ) : (genericRegion T).Nonempty :=
  ⟨EconomicFamily.parameterWitness T, exceptionalProduct_witness T⟩

theorem genericRegion_open (T : ℕ) : IsOpen (genericRegion T) :=
  PanelMoments.analytic_nonzero_open (exceptionalProduct_analytic T)

theorem genericRegion_dense (T : ℕ) : Dense (genericRegion T) :=
  PanelMoments.analytic_nonzero_dense (exceptionalProduct_analytic T)
    (exceptionalProduct_witness T)

theorem region_localNondegenerate {T : ℕ} {θ : Parameter T}
    (hθ : θ ∈ genericRegion T) (t : Blocks T) :
    LocalNondegenerate (coefficientVectors θ t) :=
  ((exceptionalProduct_ne_zero_iff θ).mp hθ).1 t

theorem region_crossNonincident {T : ℕ} {θ : Parameter T}
    (hθ : θ ∈ genericRegion T) : CrossNonincident (coefficientVectors θ) :=
  ((exceptionalProduct_ne_zero_iff θ).mp hθ).2.1

theorem region_lineConditions {T : ℕ} {θ : Parameter T}
    (hθ : θ ∈ genericRegion T) (t : Blocks T) :
    CubicRelations.LineConditions (blockA θ t) (blockB θ t) where
  nonCoordinate r := Or.inl (ne_of_gt (blockA_pos θ t r))
  distinct r s hrs := Or.inl ((((exceptionalProduct_ne_zero_iff θ).mp hθ).2.2 t).ne hrs)

end

end PanelMoments.StructuralGenericity

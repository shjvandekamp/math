import PanelMoments.Economic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
Genericity infrastructure. These lemmas do not assume a rank conclusion.
An application must supply an actual analytic minor and its nonzero witness.
-/

namespace PanelMoments

open scoped BigOperators Topology
open Set Filter

noncomputable section

theorem analytic_nonzero_dense {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ) {w : Fin n → ℝ} (hw : f w ≠ 0) :
    Dense {x | f x ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU hne
  by_contra h
  have hz : ∀ x ∈ U, f x = 0 := by
    intro x hx
    by_contra hfx
    exact h ⟨x, hx, hfx⟩
  obtain ⟨x, hx⟩ := hne
  have he : f =ᶠ[𝓝 x] 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hz y hy
  have hall := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (Set.mem_univ x) he
  exact hw (hall (Set.mem_univ w))

theorem analytic_nonzero_open {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : AnalyticOnNhd ℝ f Set.univ) : IsOpen {x | f x ≠ 0} := by
  have hc : Continuous f := continuousOn_univ.mp hf.continuousOn
  exact isOpen_ne.preimage hc

theorem analyticAt_matrix_det {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : (Fin n → ℝ) → Matrix ι ι ℝ} {x : Fin n → ℝ}
    (hA : ∀ i j, AnalyticAt ℝ (fun z => A z i j) x) :
    AnalyticAt ℝ (fun z => (A z).det) x := by
  simp only [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  exact hA (σ i) i

/-- Four normalized state-dependence parameters, two slopes, and four scalar covariates. -/
abbrev EconomicParameter := Fin 10 → ℝ

def parameterGamma (θ : EconomicParameter) (q : Fin 2) (r : State 2) : ℝ :=
  if r = 0 then 0 else θ ⟨q.val * 2 + (r.val - 1), by omega⟩

def parameterBeta (θ : EconomicParameter) (q : Fin 2) (_ : Fin 1) : ℝ :=
  θ ⟨4 + q.val, by omega⟩

def parameterCovariate (θ : EconomicParameter) (t : ℕ) (_ : Fin 1) : ℝ :=
  if ht : t < 4 then θ ⟨6 + t, by omega⟩ else 0

def parameterTable (θ : EconomicParameter) : Table 2 :=
  economicTable (parameterGamma θ) (parameterBeta θ) (parameterCovariate θ)

@[simp] theorem parameterGamma_baseline (θ : EconomicParameter) (q : Fin 2) :
    parameterGamma θ q 0 = 0 := by simp [parameterGamma]

theorem parameterTable_positive (θ : EconomicParameter) : PositiveTable (parameterTable θ) :=
  economicTable_pos _ _ _

theorem parameterTable_analytic (t : ℕ) (r q : State 2) :
    AnalyticOnNhd ℝ (fun θ => parameterTable θ t r q) Set.univ := by
  intro θ _
  have hp (i : Fin 10) : AnalyticAt ℝ (fun z : EconomicParameter => z i) θ :=
    (ContinuousLinearMap.proj (R := ℝ) i).analyticAt θ
  have hg (i : Fin 2) : AnalyticAt ℝ (fun z => parameterGamma z i r) θ := by
    unfold parameterGamma
    split_ifs
    · exact analyticAt_const
    · exact hp _
  have hb (i : Fin 2) : AnalyticAt ℝ (fun z => parameterBeta z i 0) θ := hp _
  have hx : AnalyticAt ℝ (fun z => parameterCovariate z t 0) θ := by
    unfold parameterCovariate
    split_ifs
    · exact hp _
    · exact analyticAt_const
  refine Fin.cases ?_ (fun i => ?_) q
  · simpa [parameterTable] using (analyticAt_const :
      AnalyticAt ℝ (fun _ : EconomicParameter => (1 : ℝ)) θ)
  · simpa [parameterTable, economicTable, economicIndex, Fin.sum_univ_one] using
      ((hg i).add (hx.mul (hb i))).rexp'

/-- An economically admissible parameter point with exact integer index tables. -/
def parameterWitness : EconomicParameter :=
  ![Real.log 2, 2 * Real.log 2, 2 * Real.log 2, 4 * Real.log 2,
    1, 2, 3 * Real.log 2, 6 * Real.log 2, 9 * Real.log 2, 12 * Real.log 2]

theorem parameterWitness_index (t : Fin 4) (r q : State 2) :
    economicIndex (parameterGamma parameterWitness) (parameterBeta parameterWitness)
        (parameterCovariate parameterWitness) t.val r q =
      (((3 * (t.val + 1) + r.val) * q.val : ℕ) : ℝ) * Real.log 2 := by
  refine Fin.cases ?_ (fun q => ?_) q
  · simp [economicIndex]
  · simp only [economicIndex, Fin.cons_succ]
    fin_cases t <;> fin_cases r <;> fin_cases q <;>
      norm_num [parameterGamma, parameterBeta, parameterCovariate,
        parameterWitness, Fin.sum_univ_one] <;> ring

theorem parameterWitness_table (t : Fin 4) (r q : State 2) :
    parameterTable parameterWitness t.val r q =
      (2 : ℝ) ^ ((3 * (t.val + 1) + r.val) * q.val) := by
  change Real.exp (economicIndex (parameterGamma parameterWitness)
    (parameterBeta parameterWitness) (parameterCovariate parameterWitness) t.val r q) = _
  rw [parameterWitness_index, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]

end

end PanelMoments

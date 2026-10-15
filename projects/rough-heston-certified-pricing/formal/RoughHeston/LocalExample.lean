module

public import RoughHeston.VolterraExistence
public import RoughHeston.Approximation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A nondegenerate exact-solution and convergence witness

The parameters are `α = 3/4`, `R = -2`, `γ = ν = 1`, `ρ = -1/2`.
On frequencies `[0,1]`, the constructed exact solution stays in the unit ball
at the explicit positive maturity below. One certified base mesh and all its
dyadic refinements converge to this actual solution family. This is a
deterministic statement and does not assert a stochastic transform identity.
-/

@[expose] public section
noncomputable section
open Set

namespace RoughHeston

def localExampleMaturity : ℝ := (Real.Gamma (7 / 4) / 16) ^ (4 / 3 : ℝ)

theorem localExampleMaturity_pos : 0 < localExampleMaturity := by
  apply Real.rpow_pos_of_pos
  exact div_pos (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 7 / 4)) (by norm_num)

theorem localExample_kernel_mass :
    localExampleMaturity ^ (3 / 4 : ℝ) / Real.Gamma (7 / 4) = 1 / 16 := by
  have hg : 0 < Real.Gamma (7 / 4) := Real.Gamma_pos_of_pos (by norm_num)
  unfold localExampleMaturity
  rw [← Real.rpow_mul (div_nonneg hg.le (by norm_num))]
  norm_num
  field_simp [ne_of_gt hg]

theorem localExample_force_bound : finiteBandForceBound (-2) 1 (-1 / 2) 1 1 1 = 9 := by
  norm_num [finiteBandForceBound, bandConstantBound, bandLinearBound]

theorem localExample_lipschitz : finiteBandLipschitz (-2) 1 (-1 / 2) 1 1 1 = 7 / 2 := by
  norm_num [finiteBandLipschitz, bandLinearBound]

/-- The exact fractional Riccati solution exists for every frequency in the
nontrivial band. All ball bounds are derived from explicit numerical constants. -/
theorem localExample_solution_at {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    ∃ h : ℝ → ℂ, IsRiccatiSolution (3 / 4) (-2) 1 (-1 / 2) 1 u localExampleMaturity h ∧
      ∀ t ∈ Icc 0 localExampleMaturity, ‖h t‖ ≤ 1 := by
  have hself : finiteBandForceBound (-2) 1 (-1 / 2) 1 1 1 *
      localExampleMaturity ^ (3 / 4 : ℝ) / Real.Gamma ((3 / 4 : ℝ) + 1) ≤ 1 := by
    rw [localExample_force_bound]
    norm_num only
    calc
      _ = 9 * (localExampleMaturity ^ (3 / 4 : ℝ) / Real.Gamma (7 / 4)) := by ring
      _ = 9 / 16 := by rw [localExample_kernel_mass]; ring
      _ ≤ 1 := by norm_num
  have hcontract : localExampleMaturity ^ (3 / 4 : ℝ) /
      Real.Gamma ((3 / 4 : ℝ) + 1) * finiteBandLipschitz (-2) 1 (-1 / 2) 1 1 1 < 1 := by
    rw [localExample_lipschitz]
    norm_num only
    rw [localExample_kernel_mass]
    norm_num
  exact exists_riccatiSolution_on_band (by norm_num) (by norm_num)
    localExampleMaturity_pos.le (by norm_num) (by norm_num) hself hcontract
    (by simpa only [abs_of_nonneg hu.1] using hu.2)

/-- Simultaneous exact-solution witness over the whole frequency band. -/
theorem localExample_solution_family :
    ∃ h : ℝ → ℝ → ℂ, ∀ u ∈ Icc (0 : ℝ) 1,
      IsRiccatiSolution (3 / 4) (-2) 1 (-1 / 2) 1 u localExampleMaturity (h u) ∧
      ∀ t ∈ Icc 0 localExampleMaturity, ‖h u t‖ ≤ 1 := by
  classical
  refine ⟨fun u => if hu : u ∈ Icc (0 : ℝ) 1 then
    Classical.choose (localExample_solution_at hu) else fun _ => 0, ?_⟩
  intro u hu
  simpa only [dite_eq_left hu] using Classical.choose_spec (localExample_solution_at hu)

/-- A fully instantiated, nonvacuous deterministic approximation theorem:
an actual bounded solution family, a positive base mesh, and a single error
constant for all frequencies, all nodes, and every dyadic refinement. -/
theorem localExample_validated_dyadic :
    ∃ h : ℝ → ℝ → ℂ, ∃ M0 : ℕ, 0 < M0 ∧
      (∀ u ∈ Icc (0 : ℝ) 1,
        IsRiccatiSolution (3 / 4) (-2) 1 (-1 / 2) 1 u localExampleMaturity (h u) ∧
        ∀ t ∈ Icc 0 localExampleMaturity, ‖h u t‖ ≤ 1) ∧
      ∀ ell : ℕ,
        let N := 2 ^ ell * M0
        let dt := localExampleMaturity / (N : ℝ)
        ∀ u ∈ Icc (0 : ℝ) 1, ∀ n ≤ N,
          ‖roughState (3 / 4) dt (-2) 1 (-1 / 2) 1 u n - h u ((n : ℝ) * dt)‖ ≤
            finiteBandNodalConstant (3 / 4) localExampleMaturity (-2) 1 (-1 / 2) 1 1 2 *
              dt ^ (3 / 4 : ℝ) ∧
          ‖roughState (3 / 4) dt (-2) 1 (-1 / 2) 1 u n‖ ≤ 2 := by
  obtain ⟨h, hh⟩ := localExample_solution_family
  obtain ⟨M0, hM0, herr⟩ := riccati_dyadic_band_error (3 / 4) localExampleMaturity
    (-2) 1 (-1 / 2) 1 1 1 1 h (by norm_num) (by norm_num) localExampleMaturity_pos
    (by norm_num) (by norm_num) (by norm_num)
    (fun u hu => (hh u hu).1) (fun u hu => (hh u hu).2)
  refine ⟨h, M0, hM0, hh, ?_⟩
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using herr

/-- The same nondegenerate exact-solution witness also has a validated
dyadic approximation of the complete trapezoidal exponent and its
exponential, with `θ = V₀ = 1` and derived order `3/4`. -/
theorem localExample_validated_transform :
    ∃ h : ℝ → ℝ → ℂ, ∃ M0 : ℕ, 0 < M0 ∧
      (∀ u ∈ Icc (0 : ℝ) 1,
        IsRiccatiSolution (3 / 4) (-2) 1 (-1 / 2) 1 u localExampleMaturity (h u) ∧
        ∀ t ∈ Icc 0 localExampleMaturity, ‖h u t‖ ≤ 1) ∧
      ∀ ell : ℕ,
        let N := 2 ^ ell * M0
        let dt := localExampleMaturity / (N : ℝ)
        ∀ u ∈ Icc (0 : ℝ) 1,
          ‖(roughExponent (3 / 4) dt (-2) 1 (-1 / 2) 1 1 1 N).eval (u : ℂ) -
            exactRiccatiExponent (-2) 1 (-1 / 2) 1 1 1 u localExampleMaturity (h u)‖ ≤
              finiteBandExponentConstant (3 / 4) localExampleMaturity (-2) 1 (-1 / 2) 1 1 1 1 2 *
                dt ^ (3 / 4 : ℝ) ∧
          ‖Complex.exp ((roughExponent (3 / 4) dt (-2) 1 (-1 / 2) 1 1 1 N).eval (u : ℂ)) -
            Complex.exp (exactRiccatiExponent (-2) 1 (-1 / 2) 1 1 1 u localExampleMaturity (h u))‖ ≤
              finiteBandTransformConstant (3 / 4) localExampleMaturity (-2) 1 (-1 / 2) 1 1 1 1 2 *
                dt ^ (3 / 4 : ℝ) := by
  obtain ⟨h, hh⟩ := localExample_solution_family
  obtain ⟨M0, hM0, herr⟩ := riccati_dyadic_band_transform_error (3 / 4) localExampleMaturity
    (-2) 1 (-1 / 2) 1 1 1 1 1 1 h (by norm_num) (by norm_num) localExampleMaturity_pos
    (by norm_num) (by norm_num) (by norm_num)
    (fun u hu => (hh u hu).1) (fun u hu => (hh u hu).2)
  refine ⟨h, M0, hM0, hh, ?_⟩
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using herr

end RoughHeston

#print axioms RoughHeston.localExample_kernel_mass
#print axioms RoughHeston.localExample_solution_family
#print axioms RoughHeston.localExample_validated_dyadic
#print axioms RoughHeston.localExample_validated_transform

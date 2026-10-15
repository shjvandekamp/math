module

public import RoughHeston.Approximation
public import RoughHeston.InvariantRegion
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Trapezoidal quadrature at the exact Riccati nodes

The source quadrature condition concerns the values of the exact solution
at the mesh nodes. This estimate is separate from perturbing those nodes
to the numerical Adams solution. It follows directly from the actual
integrand's derived Hölder bound and the actual trapezoidal weights.
-/

@[expose] public section
noncomputable section
open Set

namespace RoughHeston

/-- Pure quadrature error for the exact Riccati solution. The sum uses the
exact path at every node, including both trapezoidal endpoints. -/
theorem IsRiccatiSolution.exact_trapezoid_error
    {alpha dt R gamma rho nu theta V0 u M L Q : ℝ} {N : ℕ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution alpha R gamma rho nu u ((N : ℝ) * dt) h)
    (ha : 0 < alpha) (ha1 : alpha < 1) (ht : 0 < dt) (hN : 0 < N) (hL : 0 ≤ L)
    (hforce : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖riccati R gamma rho nu u (h t)‖ ≤ M)
    (hpath : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖h t‖ ≤ Q)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q →
      ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤ L * ‖z - w‖) :
    ‖exactRiccatiExponent R gamma rho nu theta V0 u ((N : ℝ) * dt) h -
      ∑ j : Fin (N + 1), (trapezoidWeight dt N j.val : ℂ) *
        riccatiExponentIntegrand R gamma rho nu theta V0 u (h ((j.val : ℝ) * dt))‖ ≤
      ((N : ℝ) * dt) * riccatiExponentLipschitz theta gamma V0 L *
        (2 * M / Real.Gamma (alpha + 1)) * dt ^ alpha := by
  have hT : 0 ≤ (N : ℝ) * dt := mul_nonneg (Nat.cast_nonneg _) ht.le
  have hM : 0 ≤ M := (norm_nonneg _).trans (hforce 0 ⟨le_rfl, hT⟩)
  have hH : 0 ≤ riccatiExponentLipschitz theta gamma V0 L *
      (2 * M / Real.Gamma (alpha + 1)) :=
    mul_nonneg (riccatiExponentLipschitz_nonneg theta gamma V0 hL)
      (div_nonneg (mul_nonneg (by norm_num) hM)
        (Real.Gamma_pos_of_pos (by linarith : 0 < alpha + 1)).le)
  have hquad := trapezoid_consistency ha ht hH hN
    (fun t => riccatiExponentIntegrand R gamma rho nu theta V0 u (h t))
    (hh.exponentIntegrand_continuous theta V0)
    (fun s t hs hst htT => hh.exponentIntegrand_holder ha ha1 hL hforce hpath hlip hs hst htT)
  simpa only [exactRiccatiExponent, mul_assoc] using hquad

/-- For the concrete equation the source's exact-node trapezoidal rate
holds on every refinement of any positive original mesh. The constant is
strictly positive and independent of the refinement level. All state and
force bounds are obtained from the equation's invariant-region theorem. -/
theorem concrete_original_dyadic_exact_quadrature_error
    (alpha T : ℝ) (h : ℝ → ℝ → ℂ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T)
    (hsol : ∀ u : ℝ, IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u T (h u))
    (M0 : ℕ) (hM0 : 0 < M0) (u : ℝ) :
    ∃ Ct : ℝ, 0 < Ct ∧ ∀ ell : ℕ,
      let N := 2 ^ ell * M0
      let dt := T / (N : ℝ)
      ‖exactRiccatiExponent (-2) 1 (-1 / 2) 1 1 1 u T (h u) -
        ∑ j : Fin (N + 1), (trapezoidWeight dt N j.val : ℂ) *
          riccatiExponentIntegrand (-2) 1 (-1 / 2) 1 1 1 u (h u ((j.val : ℝ) * dt))‖ ≤
        Ct * dt ^ alpha := by
  let Q := bandConstantBound (-2) |u| + 1
  let M := finiteBandForceBound (-2) 1 (-1 / 2) 1 |u| Q
  let L := finiteBandLipschitz (-2) 1 (-1 / 2) 1 |u| Q
  let C := T * riccatiExponentLipschitz 1 1 1 L * (2 * M / Real.Gamma (alpha + 1))
  have hQ : 0 ≤ Q := by dsimp [Q, bandConstantBound]; positivity
  have hM : 0 ≤ M := finiteBandForceBound_nonneg (-2) 1 (-1 / 2) 1 (abs_nonneg u) hQ
  have hL : 0 ≤ L := finiteBandLipschitz_nonneg (-2) 1 (-1 / 2) 1 (abs_nonneg u) hQ
  have hC : 0 ≤ C :=
    mul_nonneg (mul_nonneg hT.le (riccatiExponentLipschitz_nonneg 1 1 1 hL))
      (div_nonneg (mul_nonneg (by norm_num) hM)
        (Real.Gamma_pos_of_pos (by linarith : 0 < alpha + 1)).le)
  have hpath : ∀ t ∈ Icc 0 T, ‖h u t‖ ≤ Q :=
    fun t ht => ((hsol u).concrete_norm_lt_band ha ha1 hT.le (le_refl |u|) t ht).le
  have hforce : ∀ t ∈ Icc 0 T, ‖riccati (-2) 1 (-1 / 2) 1 u (h u t)‖ ≤ M :=
    fun t ht => riccati_band_norm_le (le_refl |u|) hQ (hpath t ht)
  have hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q →
      ‖riccati (-2) 1 (-1 / 2) 1 u z - riccati (-2) 1 (-1 / 2) 1 u w‖ ≤ L * ‖z - w‖ :=
    fun _ _ hz hw => riccati_band_lipschitz (le_refl |u|) hz hw
  refine ⟨C + 1, by linarith, fun ell => ?_⟩
  let N := 2 ^ ell * M0
  let dt := T / (N : ℝ)
  have hN : 0 < N := Nat.mul_pos (pow_pos (by norm_num) _) hM0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdt : 0 < dt := div_pos hT hNr
  have hNd : (N : ℝ) * dt = T := by dsimp [dt]; field_simp
  have hh : IsRiccatiSolution alpha (-2) 1 (-1 / 2) 1 u ((N : ℝ) * dt) (h u) := by
    rw [hNd]
    exact hsol u
  have hquad := hh.exact_trapezoid_error (theta := 1) (V0 := 1)
    ha ha1 hdt hN hL (by rw [hNd]; exact hforce) (by rw [hNd]; exact hpath) hlip
  rw [hNd] at hquad
  exact hquad.trans (mul_le_mul_of_nonneg_right (show C ≤ C + 1 by linarith)
    (Real.rpow_nonneg hdt.le alpha))

end RoughHeston

#print axioms RoughHeston.IsRiccatiSolution.exact_trapezoid_error
#print axioms RoughHeston.concrete_original_dyadic_exact_quadrature_error

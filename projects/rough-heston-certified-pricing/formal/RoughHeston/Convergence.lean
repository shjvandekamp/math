module

public import RoughHeston.Volterra
public import RoughHeston.NodalError
public import RoughHeston.ProductIntegration
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Nodal error derived from the actual fractional Riccati equation

The regularity and both consistency defects are proved, rather than supplied
as solver hypotheses. Existence and boundedness of the exact solution are
separate domain assumptions in these deterministic convergence statements.
-/

@[expose] public section
noncomputable section
open Set Finset

namespace RoughHeston

def riccatiDefectBound (alpha dt M L : ℝ) (N : ℕ) : ℝ :=
  (L * (2 * M / Real.Gamma (alpha + 1))) * adamsRowMass alpha dt N * dt ^ alpha

theorem adamsRowMass_eq_maturity {alpha dt T : ℝ} {N : ℕ}
    (ht : 0 ≤ dt) (hT : (N : ℝ) * dt = T) :
    adamsRowMass alpha dt N = T ^ alpha / Real.Gamma (alpha + 1) := by
  rw [← hT, Real.mul_rpow (Nat.cast_nonneg _) ht]
  unfold adamsRowMass
  ring

theorem riccatiDefectBound_eq_maturity {alpha dt T M L : ℝ} {N : ℕ}
    (ht : 0 ≤ dt) (hT : (N : ℝ) * dt = T) :
    riccatiDefectBound alpha dt M L N =
      (L * (2 * M / Real.Gamma (alpha + 1)) * (T ^ alpha / Real.Gamma (alpha + 1))) * dt ^ alpha := by
  rw [riccatiDefectBound, adamsRowMass_eq_maturity ht hT]

theorem riccatiDefectBound_nonneg {alpha dt M L : ℝ} (N : ℕ)
    (ha : 0 < alpha) (ht : 0 < dt) (hM : 0 ≤ M) (hL : 0 ≤ L) :
    0 ≤ riccatiDefectBound alpha dt M L N := by
  unfold riccatiDefectBound adamsRowMass
  have hG := (Real.Gamma_pos_of_pos (show 0 < alpha + 1 by linarith)).le
  positivity

/-- The two actual Adams exact-data residuals, with a derived uniform
`dt^alpha` bound. This theorem includes the corrector endpoint. -/
theorem IsRiccatiSolution.adams_consistency {alpha dt R gamma rho nu u M L Q : ℝ}
    {N : ℕ} {h : ℝ → ℂ}
    (hh : IsRiccatiSolution alpha R gamma rho nu u ((N : ℝ) * dt) h)
    (ha : 0 < alpha) (ha1 : alpha < 1) (ht : 0 < dt)
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hbound : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖riccati R gamma rho nu u (h t)‖ ≤ M)
    (hhbound : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖h t‖ ≤ Q)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q →
      ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤ L * ‖z - w‖)
    {n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (‖(∑ j : Fin n, (predictorWeight alpha dt j.val n : ℂ) *
        riccati R gamma rho nu u (h ((j.val : ℝ) * dt))) - h ((n : ℝ) * dt)‖ ≤
      riccatiDefectBound alpha dt M L N) ∧
    (‖(∑ j : Fin n, (correctorWeight alpha dt j.val n : ℂ) *
        riccati R gamma rho nu u (h ((j.val : ℝ) * dt))) +
        (correctorWeight alpha dt n n : ℂ) * riccati R gamma rho nu u (h ((n : ℝ) * dt)) -
        h ((n : ℝ) * dt)‖ ≤ riccatiDefectBound alpha dt M L N) := by
  let H := L * (2 * M / Real.Gamma (alpha + 1))
  have hG : 0 < Real.Gamma (alpha + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have htn : 0 ≤ (n : ℝ) * dt := mul_nonneg (Nat.cast_nonneg _) ht.le
  have htnT : (n : ℝ) * dt ≤ (N : ℝ) * dt :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hnN) ht.le
  have hf : ContinuousOn (fun t => riccati R gamma rho nu u (h t))
      (Icc 0 ((n : ℝ) * dt)) := hh.force_continuous.mono (Icc_subset_Icc le_rfl htnT)
  have hholder : ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ (n : ℝ) * dt →
      ‖riccati R gamma rho nu u (h r) - riccati R gamma rho nu u (h s)‖ ≤ H * (r - s) ^ alpha := by
    intro s r hs hsr hr
    simpa only [H, mul_assoc] using
      hh.force_holder ha ha1 hL hbound hhbound hlip hs hsr (hr.trans htnT)
  have hp := predictor_consistency_fin ha ht hH n
    (fun t => riccati R gamma rho nu u (h t)) hf hholder
  have hc := corrector_consistency_fin ha ht hH hn
    (fun t => riccati R gamma rho nu u (h t)) hf hholder
  have hsol := hh.2 ((n : ℝ) * dt) ⟨htn, htnT⟩
  rw [← hsol, norm_sub_rev] at hp hc
  have hbound' : H * ((n : ℝ) * dt) ^ alpha / Real.Gamma (alpha + 1) * dt ^ alpha ≤
      riccatiDefectBound alpha dt M L N := by
    calc
      _ = H * adamsRowMass alpha dt n * dt ^ alpha := by
        rw [Real.mul_rpow (Nat.cast_nonneg _) ht.le]
        unfold adamsRowMass
        ring
      _ ≤ H * adamsRowMass alpha dt N * dt ^ alpha :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (adamsRowMass_mono ha ht hnN) hH)
          (Real.rpow_nonneg ht.le _)
  constructor
  · simpa only [Complex.real_smul] using hp.trans hbound'
  · rw [Fin.sum_univ_castSucc] at hc
    simpa only [Fin.val_castSucc, Fin.val_last, Complex.real_smul] using hc.trans hbound'

/-- Conservative nodal order `alpha` for the concrete PECE scheme on a
contraction horizon. Every consistency premise has been discharged from
the defining Volterra equation and its derived Hölder bound. -/
theorem riccati_local_nodal_error (alpha dt R gamma rho nu u : ℝ) (N : ℕ)
    (h : ℝ → ℂ) {Q M L : ℝ}
    (hh : IsRiccatiSolution alpha R gamma rho nu u ((N : ℝ) * dt) h)
    (ha : 0 < alpha) (ha1 : alpha < 1) (ht : 0 < dt)
    (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hsmall : adamsRowMass alpha dt N * M ≤ Q)
    (hcontract : adamsRowMass alpha dt N * L < 1)
    (hFbound : ∀ z : ℂ, ‖z‖ ≤ Q → ‖riccati R gamma rho nu u z‖ ≤ M)
    (hlip : ∀ z w : ℂ, ‖z‖ ≤ Q → ‖w‖ ≤ Q →
      ‖riccati R gamma rho nu u z - riccati R gamma rho nu u w‖ ≤ L * ‖z - w‖)
    (hhbound : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖h t‖ ≤ Q) :
    ∀ n ≤ N, ‖roughState alpha dt R gamma rho nu u n - h ((n : ℝ) * dt)‖ ≤
      riccatiDefectBound alpha dt M L N * (1 + adamsRowMass alpha dt N * L) /
        (1 - adamsRowMass alpha dt N * L) := by
  have hcons (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :=
    hh.adams_consistency ha ha1 ht hM hL
      (fun t ht => hFbound _ (hhbound t ht)) hhbound hlip hn hnN
  apply roughState_local_error alpha dt R gamma rho nu u
    (fun n => h ((n : ℝ) * dt)) N ha ht hQ hM hL
    (riccatiDefectBound_nonneg N ha ht hM hL) hsmall hcontract hFbound hlip
  · intro n hn
    exact hhbound _ ⟨mul_nonneg (Nat.cast_nonneg _) ht.le,
      mul_le_mul_of_nonneg_right (by exact_mod_cast hn) ht.le⟩
  · simpa only [Nat.cast_zero, zero_mul] using hh.zero (mul_nonneg (Nat.cast_nonneg _) ht.le)
  · intro n hn hnN
    exact (hcons n hn hnN).1
  · intro n hn hnN
    exact (hcons n hn hnN).2

/-- Conversion to the source paper's time-weighted nodal convention.
This does not by itself absorb any excluded coarse refinement levels. -/
theorem unweighted_error_implies_source_weighted {alpha dt t T C e : ℝ}
    (ha : alpha ≤ 1) (hdt : 0 ≤ dt) (ht : 0 < t) (htT : t ≤ T)
    (hC : 0 ≤ C) (he : e ≤ C * dt ^ alpha) :
    e ≤ (C * T ^ (1 - alpha)) * t ^ (alpha - 1) * dt ^ alpha := by
  have hT : 0 < T := ht.trans_le htT
  have hp := Real.rpow_le_rpow_of_nonpos ht htT (show alpha - 1 ≤ 0 by linarith)
  have hprod : T ^ (1 - alpha) * T ^ (alpha - 1) = 1 := by
    rw [← Real.rpow_add hT]
    simp
  have hf : 1 ≤ T ^ (1 - alpha) * t ^ (alpha - 1) := by
    calc
      1 = T ^ (1 - alpha) * T ^ (alpha - 1) := hprod.symm
      _ ≤ T ^ (1 - alpha) * t ^ (alpha - 1) :=
        mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hT.le _)
  have hm := mul_le_mul_of_nonneg_left hf
    (mul_nonneg hC (Real.rpow_nonneg hdt alpha))
  apply he.trans
  nlinarith

end RoughHeston

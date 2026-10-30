module

public import RoughHeston.Approximation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rates on every original dyadic level

Every positive original base mesh eventually satisfies the explicit
continuation threshold. Its remaining coarse levels contain only finitely
many finite numerical values, which can be absorbed in one larger constant.
This operation is pointwise in frequency and asserts no Fourier integrability
of the resulting constants.
-/

@[expose] public section
noncomputable section
open Set Finset

namespace RoughHeston

/-- A rate on a tail of levels extends to all levels when each omitted level
has finitely many nodes and the scaling factor is strictly positive. -/
theorem finite_prefix_rate_absorption (E : ℕ → ℕ → ℝ) (N : ℕ → ℕ) (w : ℕ → ℝ)
    (hw : ∀ ell, 0 < w ell) (L0 : ℕ) (C : ℝ)
    (htail : ∀ ell, L0 ≤ ell → ∀ n ≤ N ell, E ell n ≤ C * w ell) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ ell n, n ≤ N ell → E ell n ≤ C' * w ell := by
  let P := ∑ ell ∈ range L0, ∑ n ∈ range (N ell + 1), max 0 (E ell n / w ell)
  have hP : 0 ≤ P := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => le_max_left _ _))
  refine ⟨max 0 C + P, add_nonneg (le_max_left _ _) hP, ?_⟩
  intro ell n hn
  by_cases hlarge : L0 ≤ ell
  · apply (htail ell hlarge n hn).trans
    apply mul_le_mul_of_nonneg_right _ (hw ell).le
    exact (le_max_right 0 C).trans (le_add_of_nonneg_right hP)
  · have hell : ell ∈ range L0 := mem_range.mpr (by omega)
    have hnmem : n ∈ range (N ell + 1) := mem_range.mpr (by omega)
    have hentry : max 0 (E ell n / w ell) ≤ P := by
      calc
        _ ≤ ∑ k ∈ range (N ell + 1), max 0 (E ell k / w ell) :=
          single_le_sum (fun k _ => le_max_left 0 (E ell k / w ell)) hnmem
        _ ≤ P := by
          dsimp [P]
          exact single_le_sum (f := fun j => ∑ k ∈ range (N j + 1), max 0 (E j k / w j))
            (fun j _ => sum_nonneg
            (fun k _ => le_max_left 0 (E j k / w j))) hell
    have hnorm : E ell n / w ell ≤ max 0 C + P :=
      (le_max_right 0 _).trans (hentry.trans (le_add_of_nonneg_left (le_max_left _ _)))
    exact (div_le_iff₀ (hw ell)).mp hnorm

/-- Scalar version, useful for the exponent and exponential errors. -/
theorem finite_prefix_scalar_rate_absorption (E w : ℕ → ℝ)
    (hw : ∀ ell, 0 < w ell) (L0 : ℕ) (C : ℝ)
    (htail : ∀ ell, L0 ≤ ell → E ell ≤ C * w ell) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ ell, E ell ≤ C' * w ell := by
  obtain ⟨C', hC', hb⟩ := finite_prefix_rate_absorption (fun ell _ => E ell)
    (fun _ => 0) w hw L0 C (fun ell he _ _ => htail ell he)
  exact ⟨C', hC', fun ell => hb ell 0 le_rfl⟩

/-- Every original positive base mesh has a tail below any prescribed
positive threshold. No relation to a separately chosen integer seed is needed. -/
theorem original_dyadic_mesh_eventually_le {T delta : ℝ} (hT : 0 < T) (hd : 0 < delta)
    (M0 : ℕ) (hM0 : 0 < M0) :
    ∃ L0 : ℕ, ∀ ell, L0 ≤ ell →
      0 < T / ((2 ^ ell * M0 : ℕ) : ℝ) ∧ T / ((2 ^ ell * M0 : ℕ) : ℝ) ≤ delta := by
  obtain ⟨L0, hL0⟩ := exists_nat_gt (T / delta)
  refine ⟨L0, ?_⟩
  intro ell hell
  have hdenNat : 0 < 2 ^ ell * M0 := Nat.mul_pos (pow_pos (by norm_num) _) hM0
  have hden : (0 : ℝ) < ((2 ^ ell * M0 : ℕ) : ℝ) := by exact_mod_cast hdenNat
  have hlarge : L0 ≤ 2 ^ ell * M0 := by
    apply hell.trans
    apply (Nat.le_of_lt ell.lt_two_pow_self).trans
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2 ^ ell) hM0
  have hratio : T / delta ≤ ((2 ^ ell * M0 : ℕ) : ℝ) :=
    hL0.le.trans (by exact_mod_cast hlarge)
  refine ⟨div_pos hT hden, (div_le_iff₀ hden).mpr ?_⟩
  have := (div_le_iff₀ hd).mp hratio
  nlinarith

/-- The actual unchanged Adams scheme has an order-`alpha` rate on a tail
of every original dyadic family, at each fixed frequency. -/
theorem riccati_original_dyadic_tail_error (alpha T R gamma rho nu u Q0 : ℝ)
    (h : ℝ → ℂ) (M0 : ℕ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hQ0 : 0 ≤ Q0) (hM0 : 0 < M0)
    (hsol : IsRiccatiSolution alpha R gamma rho nu u T h)
    (hbound : ∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q0) :
    ∃ L0 : ℕ, ∀ ell, L0 ≤ ell →
      let N := 2 ^ ell * M0
      let dt := T / (N : ℝ)
      ∀ n ≤ N,
        ‖roughState alpha dt R gamma rho nu u n - h ((n : ℝ) * dt)‖ ≤
          finiteBandNodalConstant alpha T R gamma rho nu |u| (Q0 + 1) * dt ^ alpha ∧
        ‖roughState alpha dt R gamma rho nu u n‖ ≤ Q0 + 1 := by
  let Q := Q0 + 1
  let M := finiteBandForceBound R gamma rho nu |u| Q
  let L := finiteBandLipschitz R gamma rho nu |u| Q
  let D := finiteBandDefectConstant alpha T R gamma rho nu |u| Q
  let rate := continuationRate alpha L
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith
  have hM : 0 ≤ M := finiteBandForceBound_nonneg R gamma rho nu (abs_nonneg u) hQ
  have hL : 0 ≤ L := finiteBandLipschitz_nonneg R gamma rho nu (abs_nonneg u) hQ
  have hr : 0 < rate := continuationRate_pos _ _
  have hrL : L * rate ^ (-alpha) ≤ 1 / 8 := continuationRate_contraction ha
  obtain ⟨L0, hmesh⟩ := original_dyadic_mesh_eventually_le hT
    (continuationMeshThreshold_pos (T := T) (L := L) (D := D) ha hr (by norm_num : (0 : ℝ) < 1))
    M0 hM0
  refine ⟨L0, ?_⟩
  intro ell hell
  let N := 2 ^ ell * M0
  let dt := T / (N : ℝ)
  have hN : 0 < N := Nat.mul_pos (pow_pos (by norm_num) _) hM0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdt : 0 < dt := (hmesh ell hell).1
  have hc := continuationMeshThreshold_conditions ha hr (by norm_num : (0 : ℝ) < 1)
    hdt (hmesh ell hell).2
  have hNd : (N : ℝ) * dt = T := by dsimp [dt]; field_simp
  have hdef : riccatiDefectBound alpha dt M L N = D * dt ^ alpha :=
    riccatiDefectBound_eq_maturity hdt.le hNd
  have hs : IsRiccatiSolution alpha R gamma rho nu u ((N : ℝ) * dt) h := by
    rw [hNd]
    exact hsol
  have hb : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖h t‖ ≤ Q0 := by
    rw [hNd]
    exact hbound
  have hmarg : 4 * riccatiDefectBound alpha dt M L N *
      Real.exp (rate * ((N : ℝ) * dt)) ≤ 1 := by
    rw [hdef, hNd]
    nlinarith [hc.2.2]
  have herr := riccati_fixed_horizon_nodal_error alpha dt R gamma rho nu u rate N h hs
    ha ha1 hdt hr (by norm_num : (0 : ℝ) ≤ 1) hM hL hrL hc.1 hc.2.1 hmarg
    (fun z hz => riccati_band_norm_le (le_refl |u|) hQ hz)
    (fun z w hz hw => riccati_band_lipschitz (le_refl |u|) hz hw) hb
  dsimp only
  intro n hn
  refine ⟨?_, (herr n hn).2⟩
  apply (herr n hn).1.trans_eq
  rw [hdef, hNd]
  unfold finiteBandNodalConstant
  dsimp [D, rate, L, Q]
  ring

/-- At each fixed frequency, a bounded actual solution yields one finite
constant covering every node of every original dyadic level, including the
unrestricted coarse meshes. -/
theorem riccati_original_dyadic_nodal_error (alpha T R gamma rho nu u Q0 : ℝ)
    (h : ℝ → ℂ) (M0 : ℕ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hQ0 : 0 ≤ Q0) (hM0 : 0 < M0)
    (hsol : IsRiccatiSolution alpha R gamma rho nu u T h)
    (hbound : ∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ell : ℕ,
      let N := 2 ^ ell * M0
      let dt := T / (N : ℝ)
      ∀ n ≤ N, ‖roughState alpha dt R gamma rho nu u n - h ((n : ℝ) * dt)‖ ≤ C * dt ^ alpha := by
  obtain ⟨L0, htail⟩ := riccati_original_dyadic_tail_error alpha T R gamma rho nu u Q0 h M0
    ha ha1 hT hQ0 hM0 hsol hbound
  let N : ℕ → ℕ := fun ell => 2 ^ ell * M0
  let dt : ℕ → ℝ := fun ell => T / (N ell : ℝ)
  have hw : ∀ ell, 0 < (dt ell) ^ alpha := by
    intro ell
    apply Real.rpow_pos_of_pos
    exact div_pos hT (by exact_mod_cast Nat.mul_pos (pow_pos (by norm_num : (0 : ℕ) < 2) ell) hM0)
  obtain ⟨C, hC, hb⟩ := finite_prefix_rate_absorption
    (fun ell n => ‖roughState alpha (dt ell) R gamma rho nu u n - h ((n : ℝ) * dt ell)‖)
    N (fun ell => (dt ell) ^ alpha) hw L0
    (finiteBandNodalConstant alpha T R gamma rho nu |u| (Q0 + 1))
    (fun ell hell n hn => (htail ell hell n hn).1)
  exact ⟨C, hC, fun ell n hn => hb ell n hn⟩

/-- The all-original-level rate also implies the source's singular-time
shape at every positive time node. The enlarged constant is still finite. -/
theorem riccati_original_dyadic_time_weighted_error (alpha T R gamma rho nu u Q0 : ℝ)
    (h : ℝ → ℂ) (M0 : ℕ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hQ0 : 0 ≤ Q0) (hM0 : 0 < M0)
    (hsol : IsRiccatiSolution alpha R gamma rho nu u T h)
    (hbound : ∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ell : ℕ,
      let N := 2 ^ ell * M0
      let dt := T / (N : ℝ)
      ∀ n, 0 < n → n ≤ N →
        ‖roughState alpha dt R gamma rho nu u n - h ((n : ℝ) * dt)‖ ≤
          C * ((n : ℝ) * dt) ^ (alpha - 1) * dt ^ alpha := by
  obtain ⟨C, hC, hb⟩ := riccati_original_dyadic_nodal_error alpha T R gamma rho nu u Q0 h M0
    ha ha1 hT hQ0 hM0 hsol hbound
  refine ⟨C * T ^ (1 - alpha), mul_nonneg hC (Real.rpow_nonneg hT.le _), ?_⟩
  intro ell
  dsimp only
  intro n hn hnN
  let N := 2 ^ ell * M0
  let dt := T / (N : ℝ)
  have hN : 0 < N := Nat.mul_pos (pow_pos (by norm_num) _) hM0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdt : 0 < dt := div_pos hT hNr
  have ht : 0 < (n : ℝ) * dt := mul_pos (by exact_mod_cast hn) hdt
  have hNd : (N : ℝ) * dt = T := by dsimp [dt]; field_simp
  have htT : (n : ℝ) * dt ≤ T := by
    rw [← hNd]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hnN) hdt.le
  have hp : T ^ (alpha - 1) ≤ ((n : ℝ) * dt) ^ (alpha - 1) :=
    Real.rpow_le_rpow_of_nonpos ht htT (by linarith)
  have hcancel : T ^ (1 - alpha) * T ^ (alpha - 1) = 1 := by
    rw [← Real.rpow_add hT, show 1 - alpha + (alpha - 1) = 0 by ring, Real.rpow_zero]
  have hfactor : 1 ≤ T ^ (1 - alpha) * ((n : ℝ) * dt) ^ (alpha - 1) := by
    calc
      1 = T ^ (1 - alpha) * T ^ (alpha - 1) := hcancel.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hT.le _)
  calc
    _ ≤ C * dt ^ alpha := hb ell n hnN
    _ ≤ (C * dt ^ alpha) * (T ^ (1 - alpha) * ((n : ℝ) * dt) ^ (alpha - 1)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor
        (mul_nonneg hC (Real.rpow_nonneg hdt.le _))
    _ = _ := by ring

/-- The actual exponent and its exponential have derived rates on a tail
of any prescribed original base mesh. -/
theorem riccati_original_dyadic_tail_transform
    (alpha T R gamma rho nu theta V0 u Q0 : ℝ) (h : ℝ → ℂ) (M0 : ℕ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hQ0 : 0 ≤ Q0) (hM0 : 0 < M0)
    (hsol : IsRiccatiSolution alpha R gamma rho nu u T h)
    (hbound : ∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q0) :
    ∃ L0 : ℕ, ∀ ell, L0 ≤ ell →
      let N := 2 ^ ell * M0
      let dt := T / (N : ℝ)
      ‖(roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ) -
        exactRiccatiExponent R gamma rho nu theta V0 u T h‖ ≤
          finiteBandExponentConstant alpha T R gamma rho nu theta V0 |u| (Q0 + 1) * dt ^ alpha ∧
      ‖Complex.exp ((roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ)) -
        Complex.exp (exactRiccatiExponent R gamma rho nu theta V0 u T h)‖ ≤
          finiteBandTransformConstant alpha T R gamma rho nu theta V0 |u| (Q0 + 1) * dt ^ alpha := by
  let Q := Q0 + 1
  let M := finiteBandForceBound R gamma rho nu |u| Q
  let L := finiteBandLipschitz R gamma rho nu |u| Q
  let Ch := finiteBandNodalConstant alpha T R gamma rho nu |u| Q
  let Cg := finiteBandExponentConstant alpha T R gamma rho nu theta V0 |u| Q
  have hQ : 0 ≤ Q := by dsimp [Q]; linarith
  have hM : 0 ≤ M := finiteBandForceBound_nonneg R gamma rho nu (abs_nonneg u) hQ
  have hL : 0 ≤ L := finiteBandLipschitz_nonneg R gamma rho nu (abs_nonneg u) hQ
  have hGamma : 0 < Real.Gamma (alpha + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hCh : 0 ≤ Ch := by
    change 0 ≤ 4 * (L * (2 * M / Real.Gamma (alpha + 1)) *
      (T ^ alpha / Real.Gamma (alpha + 1))) * Real.exp (continuationRate alpha L * T)
    positivity
  have hCg : 0 ≤ Cg := by
    change 0 ≤ T * riccatiExponentLipschitz theta gamma V0 L *
      (Ch + 2 * M / Real.Gamma (alpha + 1))
    exact mul_nonneg (mul_nonneg hT.le (riccatiExponentLipschitz_nonneg theta gamma V0 hL))
      (add_nonneg hCh (by positivity))
  obtain ⟨L0, hnodes⟩ := riccati_original_dyadic_tail_error alpha T R gamma rho nu u Q0 h M0
    ha ha1 hT hQ0 hM0 hsol hbound
  refine ⟨L0, ?_⟩
  intro ell hell
  let N := 2 ^ ell * M0
  let dt := T / (N : ℝ)
  have hN : 0 < N := Nat.mul_pos (pow_pos (by norm_num) _) hM0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hdt : 0 < dt := div_pos hT hNr
  have hdtT : dt ≤ T := div_le_self hT.le (by exact_mod_cast hN)
  have hNd : (N : ℝ) * dt = T := by dsimp [dt]; field_simp
  have hs : IsRiccatiSolution alpha R gamma rho nu u ((N : ℝ) * dt) h := by
    rw [hNd]
    exact hsol
  have hpath : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖h t‖ ≤ Q := by
    rw [hNd]
    exact fun t ht => (hbound t ht).trans (by dsimp [Q]; linarith)
  have hforce : ∀ t ∈ Icc 0 ((N : ℝ) * dt), ‖riccati R gamma rho nu u (h t)‖ ≤ M :=
    fun t ht => riccati_band_norm_le (le_refl |u|) hQ (hpath t ht)
  have hg0 := hs.roughExponent_error (theta := theta) (V0 := V0) ha ha1 hdt hN hL
    hforce hpath (fun n hn => (hnodes ell hell n hn).2)
    (fun z w hz hw => riccati_band_lipschitz (le_refl |u|) hz hw)
    (fun n hn => (hnodes ell hell n hn).1)
  have hg : ‖(roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ) -
      exactRiccatiExponent R gamma rho nu theta V0 u ((N : ℝ) * dt) h‖ ≤ Cg * dt ^ alpha := by
    apply hg0.trans_eq
    rw [hNd]
    change T * riccatiExponentLipschitz theta gamma V0 L *
      (Ch * dt ^ alpha + (2 * M / Real.Gamma (alpha + 1)) * dt ^ alpha) = _
    dsimp [Cg, finiteBandExponentConstant, Ch, M, L]
    ring
  dsimp only
  refine ⟨by simpa only [hNd] using hg, ?_⟩
  have htform := roughTransform_error_of_exponent_error hdt.le hpath hforce hg
  have hpow : dt ^ alpha ≤ T ^ alpha := Real.rpow_le_rpow hdt.le hdtT ha.le
  have hD : 0 ≤ Cg * dt ^ alpha := mul_nonneg hCg (Real.rpow_nonneg hdt.le _)
  calc
    _ ≤ Real.exp (T * (|theta * gamma| * Q + |V0| * M) + Cg * dt ^ alpha) *
        (Cg * dt ^ alpha) := by simpa only [hNd] using htform
    _ ≤ Real.exp (T * (|theta * gamma| * Q + |V0| * M) + Cg * T ^ alpha) *
        (Cg * dt ^ alpha) := by
      apply mul_le_mul_of_nonneg_right _ hD
      apply Real.exp_le_exp.mpr
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow hCg)
    _ = _ := by
      dsimp [finiteBandTransformConstant, Cg, M, Q]
      ring

/-- At each fixed frequency, both scalar rates cover all original levels.
The constants absorb the actual coarse-level errors rather than imposing
accuracy or boundedness conditions on those coarse numerical solutions. -/
theorem riccati_original_dyadic_transform_error
    (alpha T R gamma rho nu theta V0 u Q0 : ℝ) (h : ℝ → ℂ) (M0 : ℕ)
    (ha : 0 < alpha) (ha1 : alpha < 1) (hT : 0 < T) (hQ0 : 0 ≤ Q0) (hM0 : 0 < M0)
    (hsol : IsRiccatiSolution alpha R gamma rho nu u T h)
    (hbound : ∀ t ∈ Icc 0 T, ‖h t‖ ≤ Q0) :
    ∃ Cg Cf : ℝ, 0 ≤ Cg ∧ 0 ≤ Cf ∧ ∀ ell : ℕ,
      let N := 2 ^ ell * M0
      let dt := T / (N : ℝ)
      ‖(roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ) -
        exactRiccatiExponent R gamma rho nu theta V0 u T h‖ ≤ Cg * dt ^ alpha ∧
      ‖Complex.exp ((roughExponent alpha dt R gamma rho nu theta V0 N).eval (u : ℂ)) -
        Complex.exp (exactRiccatiExponent R gamma rho nu theta V0 u T h)‖ ≤ Cf * dt ^ alpha := by
  obtain ⟨L0, htail⟩ := riccati_original_dyadic_tail_transform alpha T R gamma rho nu theta V0 u Q0 h M0
    ha ha1 hT hQ0 hM0 hsol hbound
  let N : ℕ → ℕ := fun ell => 2 ^ ell * M0
  let dt : ℕ → ℝ := fun ell => T / (N ell : ℝ)
  have hw : ∀ ell, 0 < (dt ell) ^ alpha := by
    intro ell
    apply Real.rpow_pos_of_pos
    exact div_pos hT (by exact_mod_cast Nat.mul_pos (pow_pos (by norm_num : (0 : ℕ) < 2) ell) hM0)
  obtain ⟨Cg, hCg, hg⟩ := finite_prefix_scalar_rate_absorption
    (fun ell => ‖(roughExponent alpha (dt ell) R gamma rho nu theta V0 (N ell)).eval (u : ℂ) -
      exactRiccatiExponent R gamma rho nu theta V0 u T h‖)
    (fun ell => (dt ell) ^ alpha) hw L0
    (finiteBandExponentConstant alpha T R gamma rho nu theta V0 |u| (Q0 + 1))
    (fun ell hell => (htail ell hell).1)
  obtain ⟨Cf, hCf, hf⟩ := finite_prefix_scalar_rate_absorption
    (fun ell => ‖Complex.exp ((roughExponent alpha (dt ell) R gamma rho nu theta V0 (N ell)).eval (u : ℂ)) -
      Complex.exp (exactRiccatiExponent R gamma rho nu theta V0 u T h)‖)
    (fun ell => (dt ell) ^ alpha) hw L0
    (finiteBandTransformConstant alpha T R gamma rho nu theta V0 |u| (Q0 + 1))
    (fun ell hell => (htail ell hell).2)
  exact ⟨Cg, Cf, hCg, hCf, fun ell => ⟨hg ell, hf ell⟩⟩

end RoughHeston

#print axioms RoughHeston.finite_prefix_rate_absorption
#print axioms RoughHeston.riccati_original_dyadic_tail_error
#print axioms RoughHeston.riccati_original_dyadic_nodal_error
#print axioms RoughHeston.riccati_original_dyadic_time_weighted_error
#print axioms RoughHeston.riccati_original_dyadic_transform_error

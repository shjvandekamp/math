module

public import RoughHeston.Exponent
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Deterministic stability of one predictor and one corrector

The estimates here expose the actual history sums. The consistency defects
are explicitly the differences between the comparison node and its two
product-integration formulas. They are not asserted to be small by a solver
interface. Analytic bounds for those differences are a separate obligation.
-/

@[expose] public section
noncomputable section
open Finset

namespace RoughHeston

def quadraticForce (q l : ℂ) (c : ℝ) (z : ℂ) : ℂ := q + l * z + (c : ℂ) * z ^ 2

theorem quadraticForce_norm_le (q l : ℂ) {c Q : ℝ}
    (hc : 0 ≤ c) (_hQ : 0 ≤ Q) {z : ℂ} (hz : ‖z‖ ≤ Q) :
    ‖quadraticForce q l c z‖ ≤ ‖q‖ + ‖l‖ * Q + c * Q ^ 2 := by
  calc
    ‖quadraticForce q l c z‖ ≤ ‖q‖ + ‖l * z‖ + ‖(c : ℂ) * z ^ 2‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖q‖ + ‖l‖ * ‖z‖ + c * ‖z‖ ^ 2 := by
      simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ ‖q‖ + ‖l‖ * Q + c * Q ^ 2 := by
      gcongr

theorem quadraticForce_lipschitz (q l : ℂ) {c Q : ℝ}
    (hc : 0 ≤ c) {z w : ℂ} (hz : ‖z‖ ≤ Q) (hw : ‖w‖ ≤ Q) :
    ‖quadraticForce q l c z - quadraticForce q l c w‖ ≤
      (‖l‖ + 2 * c * Q) * ‖z - w‖ := by
  have hid : quadraticForce q l c z - quadraticForce q l c w =
      (l + (c : ℂ) * (z + w)) * (z - w) := by
    unfold quadraticForce
    ring
  rw [hid, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖l + (c : ℂ) * (z + w)‖ ≤ ‖l‖ + ‖(c : ℂ) * (z + w)‖ := norm_add_le _ _
    _ = ‖l‖ + c * ‖z + w‖ := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ ‖l‖ + c * (‖z‖ + ‖w‖) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_add_le z w) hc)
    _ ≤ ‖l‖ + 2 * c * Q := by nlinarith

/-- The finite weighted history used by both stages of the scheme. -/
def weightedHistory {n : ℕ} (w : Fin n → ℝ) (F : ℂ → ℂ) (x : Fin n → ℂ) : ℂ :=
  ∑ j, (w j : ℂ) * F (x j)

theorem weightedHistory_norm_le {n : ℕ} (w : Fin n → ℝ) (F : ℂ → ℂ)
    (x : Fin n → ℂ) (M : ℝ) (hw : ∀ j, 0 ≤ w j) (hF : ∀ j, ‖F (x j)‖ ≤ M) :
    ‖weightedHistory w F x‖ ≤ (∑ j, w j) * M := by
  unfold weightedHistory
  calc
    ‖∑ j, (w j : ℂ) * F (x j)‖ ≤ ∑ j, ‖(w j : ℂ) * F (x j)‖ := norm_sum_le _ _
    _ = ∑ j, w j * ‖F (x j)‖ := by
      congr 1
      funext j
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j)]
    _ ≤ ∑ j, w j * M := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hF j) (hw j)
    _ = (∑ j, w j) * M := (sum_mul ..).symm

theorem weightedHistory_sub_le {n : ℕ} (w : Fin n → ℝ) (F : ℂ → ℂ)
    (x y : Fin n → ℂ) (d : Fin n → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hF : ∀ j, ‖F (x j) - F (y j)‖ ≤ d j) :
    ‖weightedHistory w F x - weightedHistory w F y‖ ≤ ∑ j, w j * d j := by
  have hid : weightedHistory w F x - weightedHistory w F y =
      ∑ j, (w j : ℂ) * (F (x j) - F (y j)) := by
    simp [weightedHistory, mul_sub, sum_sub_distrib]
  rw [hid]
  calc
    ‖∑ j, (w j : ℂ) * (F (x j) - F (y j))‖ ≤
        ∑ j, ‖(w j : ℂ) * (F (x j) - F (y j))‖ := norm_sum_le _ _
    _ = ∑ j, w j * ‖F (x j) - F (y j)‖ := by
      congr 1
      funext j
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j)]
    _ ≤ ∑ j, w j * d j := sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hF j) (hw j)

def singleCorrection {n : ℕ} (a b : Fin n → ℝ) (ae : ℝ)
    (F : ℂ → ℂ) (x : Fin n → ℂ) : ℂ :=
  weightedHistory a F x + (ae : ℂ) * F (weightedHistory b F x)

/-- A positive row with bounded total mass maps a force-bounded ball into
itself at both stages. This is an estimate for the specified explicit step. -/
theorem singleCorrection_ball {n : ℕ} (a b : Fin n → ℝ) (ae : ℝ)
    (F : ℂ → ℂ) (x : Fin n → ℂ) {Q M κ : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (he : 0 ≤ ae)
    (hM : 0 ≤ M) (hrowA : (∑ j, a j) + ae ≤ κ) (hrowB : (∑ j, b j) ≤ κ)
    (hball : κ * M ≤ Q) (hx : ∀ j, ‖x j‖ ≤ Q)
    (hF : ∀ z : ℂ, ‖z‖ ≤ Q → ‖F z‖ ≤ M) :
    ‖weightedHistory b F x‖ ≤ Q ∧ ‖singleCorrection a b ae F x‖ ≤ Q := by
  have hp : ‖weightedHistory b F x‖ ≤ Q :=
    (weightedHistory_norm_le b F x M hb (fun j => hF _ (hx j))).trans
      ((mul_le_mul_of_nonneg_right hrowB hM).trans hball)
  refine ⟨hp, ?_⟩
  calc
    ‖singleCorrection a b ae F x‖ ≤
        ‖weightedHistory a F x‖ + ‖(ae : ℂ) * F (weightedHistory b F x)‖ := norm_add_le _ _
    _ = ‖weightedHistory a F x‖ + ae * ‖F (weightedHistory b F x)‖ := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
    _ ≤ (∑ j, a j) * M + ae * M := add_le_add
      (weightedHistory_norm_le a F x M ha (fun j => hF _ (hx j)))
      (mul_le_mul_of_nonneg_left (hF _ hp) he)
    _ = ((∑ j, a j) + ae) * M := by ring
    _ ≤ κ * M := mul_le_mul_of_nonneg_right hrowA hM
    _ ≤ Q := hball

/-- The complete error in a PECE step, including the predicted endpoint.
`dp` and `dc` bound explicit exact-data residuals displayed in the premises. -/
theorem singleCorrection_error {n : ℕ} (a b : Fin n → ℝ) (ae : ℝ)
    (F : ℂ → ℂ) (x y : Fin n → ℂ) (yn : ℂ) (d : Fin n → ℝ)
    {L dp dc : ℝ} (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (he : 0 ≤ ae) (hL : 0 ≤ L)
    (hF : ∀ j, ‖F (x j) - F (y j)‖ ≤ L * d j)
    (hpred : ‖weightedHistory b F y - yn‖ ≤ dp)
    (hcorr : ‖weightedHistory a F y + (ae : ℂ) * F yn - yn‖ ≤ dc)
    (hendpoint : ‖F (weightedHistory b F x) - F yn‖ ≤
      L * ‖weightedHistory b F x - yn‖) :
    ‖singleCorrection a b ae F x - yn‖ ≤
      dc + (∑ j, a j * (L * d j)) + ae * L * (dp + ∑ j, b j * (L * d j)) := by
  have hp : ‖weightedHistory b F x - yn‖ ≤ dp + ∑ j, b j * (L * d j) := by
    calc
      ‖weightedHistory b F x - yn‖ ≤
          ‖weightedHistory b F x - weightedHistory b F y‖ +
            ‖weightedHistory b F y - yn‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ (∑ j, b j * (L * d j)) + dp :=
        add_le_add (weightedHistory_sub_le b F x y _ hb hF) hpred
      _ = _ := by ring
  have hid : singleCorrection a b ae F x - yn =
      (weightedHistory a F y + (ae : ℂ) * F yn - yn) +
      (weightedHistory a F x - weightedHistory a F y) +
      (ae : ℂ) * (F (weightedHistory b F x) - F yn) := by
    unfold singleCorrection
    ring
  rw [hid]
  calc
    ‖_ + _ + _‖ ≤
        ‖weightedHistory a F y + (ae : ℂ) * F yn - yn‖ +
        ‖weightedHistory a F x - weightedHistory a F y‖ +
        ‖(ae : ℂ) * (F (weightedHistory b F x) - F yn)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖weightedHistory a F y + (ae : ℂ) * F yn - yn‖ +
        ‖weightedHistory a F x - weightedHistory a F y‖ +
        ae * ‖F (weightedHistory b F x) - F yn‖ := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
    _ ≤ dc + (∑ j, a j * (L * d j)) + ae *
        (L * (dp + ∑ j, b j * (L * d j))) := by
      exact add_le_add (add_le_add hcorr (weightedHistory_sub_le a F x y _ ha hF))
        (mul_le_mul_of_nonneg_left
          (hendpoint.trans (mul_le_mul_of_nonneg_left hp hL)) he)
    _ = _ := by ring

/-- The unweighted local-contraction estimate, retaining the endpoint
correction. Positivity and the two row masses control its propagation. -/
theorem singleCorrection_error_uniform {n : ℕ} (a b : Fin n → ℝ) (ae : ℝ)
    (F : ℂ → ℂ) (x y : Fin n → ℂ) (yn : ℂ) {L E ε κ : ℝ}
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) (he : 0 ≤ ae)
    (hL : 0 ≤ L) (hE : 0 ≤ E) (hε : 0 ≤ ε)
    (hrowA : (∑ j, a j) + ae ≤ κ) (hrowB : (∑ j, b j) ≤ κ)
    (hcontraction : κ * L ≤ 1)
    (hF : ∀ j, ‖F (x j) - F (y j)‖ ≤ L * E)
    (hpred : ‖weightedHistory b F y - yn‖ ≤ ε)
    (hcorr : ‖weightedHistory a F y + (ae : ℂ) * F yn - yn‖ ≤ ε)
    (hendpoint : ‖F (weightedHistory b F x) - F yn‖ ≤
      L * ‖weightedHistory b F x - yn‖) :
    ‖singleCorrection a b ae F x - yn‖ ≤ ε * (1 + κ * L) + κ * L * E := by
  have hs := singleCorrection_error a b ae F x y yn (fun _ => E)
    ha hb he hL hF hpred hcorr hendpoint
  simp only [← sum_mul] at hs
  have hsa : 0 ≤ ∑ j, a j := sum_nonneg fun j _ => ha j
  have hae : ae ≤ κ := by linarith
  have hpb : L * (∑ j, b j) ≤ 1 := by nlinarith [mul_le_mul_of_nonneg_left hrowB hL]
  have hpa : L * (∑ j, a j) + ae * L ^ 2 * (∑ j, b j) ≤ κ * L := by
    have hm := mul_le_mul_of_nonneg_left hpb (mul_nonneg he hL)
    have haM := mul_le_mul_of_nonneg_left hrowA hL
    nlinarith
  have heps : ae * L * ε ≤ κ * L * ε :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hae hL) hε
  have herr := mul_le_mul_of_nonneg_right hpa hE
  nlinarith

end RoughHeston

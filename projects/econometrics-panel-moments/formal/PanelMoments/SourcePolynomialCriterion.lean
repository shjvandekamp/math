import PanelMoments.SourcePolynomialKernels
import PanelMoments.SourceHomogeneousCriterion
import PanelMoments.Polynomial

set_option autoImplicit false

/-!
# Polynomial columns in the actual source induction criterion

Evaluation on positive homogeneous coordinates is injective on polynomial
rows. The common tail denominator is positive there, so clearing it preserves
exactly the constant-real linear relations. The remaining source-induction
premise can therefore be stated on the explicit polynomial reduced columns.
Their independence remains an explicit hypothesis, not a conclusion here.
-/

namespace PanelMoments.SourcePolynomialCriterion

open SourceHomogeneous SourceHomogeneousCriterion SourcePolynomialKernels

noncomputable section

abbrev PolynomialImageSpace := State 2 → Poly

def positiveEvaluation : PolynomialImageSpace →ₗ[ℝ] HomogeneousImageSpace where
  toFun p c X := MvPolynomial.aeval X.val (p c)
  map_add' p q := by
    funext c X
    exact map_add (MvPolynomial.aeval X.val) (p c) (q c)
  map_smul' a p := by
    funext c X
    exact (MvPolynomial.aeval X.val : Poly →ₐ[ℝ] ℝ).toLinearMap.map_smul a (p c)

theorem positiveEvaluation_injective : Function.Injective positiveEvaluation := by
  intro p q h
  funext c
  apply MvPolynomial.funext_set (fun _ => Set.Ioi (0 : ℝ))
    (fun _ => Set.Ioi_infinite 0)
  intro X hX
  exact congrFun (congrFun h c) ⟨X, fun i => hX i (Set.mem_univ i)⟩

def tailScale {N : ℕ} (A : Table 2) :
    HomogeneousImageSpace →ₗ[ℝ] HomogeneousImageSpace where
  toFun f c X := MvPolynomial.eval X.val (tailDenominator (N := N) A) * f c X
  map_add' f g := by
    funext c X
    exact mul_add _ _ _
  map_smul' a f := by
    funext c X
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem tailScale_injective {N : ℕ} {A : Table 2} (hA : PositiveTable A) :
    Function.Injective (tailScale (N := N) A) := by
  intro f g h
  funext c X
  exact mul_left_cancel₀ (ne_of_gt (tailDenominator_eval_pos (N := N) hA X.property))
    (congrFun (congrFun h c) X)

theorem positiveEvaluation_clearedReduced {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (p : SourceNewIndices.NewParameter N) :
    positiveEvaluation (clearedReducedColumn A p) =
      tailScale (N := N) A (homogeneousReducedColumn A p) := by
  funext c X
  exact clearedReducedColumn_eval hA X.property p c

theorem linearIndependent_clearedReduced_iff {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) :
    LinearIndependent ℝ (clearedReducedColumn A :
      SourceNewIndices.NewParameter N → PolynomialImageSpace) ↔
        LinearIndependent ℝ (homogeneousReducedColumn A :
          SourceNewIndices.NewParameter N → HomogeneousImageSpace) := by
  have heval := positiveEvaluation.linearIndependent_iff
    (v := clearedReducedColumn (N := N) A)
    (LinearMap.ker_eq_bot_of_injective positiveEvaluation_injective)
  have hscale := (tailScale (N := N) A).linearIndependent_iff
    (v := homogeneousReducedColumn (N := N) A)
    (LinearMap.ker_eq_bot_of_injective (tailScale_injective hA))
  change LinearIndependent ℝ (fun p => positiveEvaluation (clearedReducedColumn A p)) ↔
    LinearIndependent ℝ (clearedReducedColumn (N := N) A) at heval
  simp only [positiveEvaluation_clearedReduced hA] at heval
  exact heval.symm.trans hscale

theorem linearIndependent_newJoint_iff_clearedReduced {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r : State 2) (hN : 2 ≤ N) :
    LinearIndependent ℝ (fun i : SourceNewIndices.NewIndex N =>
      SourceJointImage.jointFirst (T := N + 1) A r (SourceFamily.sourceMoment A r i.val)) ↔
        LinearIndependent ℝ (clearedReducedColumn A :
          SourceNewIndices.NewParameter N → PolynomialImageSpace) :=
  (linearIndependent_newJoint_iff_homogeneousReduced hA r hN).trans
    (linearIndependent_clearedReduced_iff hA).symm

theorem linearIndependent_source_of_clearedReduced {N : ℕ} {A : Table 2}
    (hA : PositiveTable A) (r : State 2) (hN : 2 ≤ N)
    (hshort : ∀ a : State 2, LinearIndependent ℝ
      (SourceFamily.sourceMoment (shift A) a :
        SourceFamily.SourceIndex N → Path 2 (N + 1) → ℝ))
    (hnew : LinearIndependent ℝ (clearedReducedColumn A :
      SourceNewIndices.NewParameter N → PolynomialImageSpace)) :
    LinearIndependent ℝ (SourceFamily.sourceMoment A r :
      SourceFamily.SourceIndex (N + 1) → Path 2 (N + 1 + 1) → ℝ) := by
  apply linearIndependent_source_of_homogeneousReduced hA r hN hshort
  exact (linearIndependent_clearedReduced_iff hA).mp hnew

end

end PanelMoments.SourcePolynomialCriterion

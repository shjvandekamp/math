import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Polynomial separation for an invariant-tail extension

For T(P) = F*P + C(P(ξ))*K, evaluation at ξ recovers P(ξ) when
F(ξ)+K(ξ) is nonzero. Three further evaluations then separate three
additional polynomial columns. Cancellation of the nonzero polynomial F
recovers P itself.

The hypotheses below are explicit polynomial evaluations and a nonzero
polynomial, not a rank or independence premise. They imply the required
node distinctions, so no separate pairwise-distinctness assumption is
needed. The argument works over any commutative integral domain.

This module proves the conditional polynomial mechanism only. The
identification of these polynomials with normalized source columns, and
verification of the structural hypotheses for the actual transfer,
remain separate obligations.
-/

namespace PanelMoments.SourceInvariantTailPolynomialExtension

noncomputable section

variable {R : Type*} [CommRing R]

def transferPolynomial (F K : Polynomial R) (ξ : R) (P : Polynomial R) :
    Polynomial R :=
  F * P + Polynomial.C (P.eval ξ) * K

def extensionPolynomial (F K N0 N1 N2 : Polynomial R) (ξ : R)
    (x y w : R) (P : Polynomial R) : Polynomial R :=
  Polynomial.C x * N0 + Polynomial.C y * N1 + Polynomial.C w * N2 +
    transferPolynomial F K ξ P

/-- The concrete evaluation conditions used to separate all four inputs. -/
structure SeparationConditions (F K N0 N1 N2 : Polynomial R)
    (ξ p0 p1 z : R) : Prop where
  N0_at_xi : N0.eval ξ = 0
  N1_at_xi : N1.eval ξ = 0
  N2_at_xi : N2.eval ξ = 0
  F_at_p0 : F.eval p0 = 0
  F_at_p1 : F.eval p1 = 0
  F_at_z : F.eval z = 0
  pivot_ne_zero : F.eval ξ + K.eval ξ ≠ 0
  N0_at_p1 : N0.eval p1 = 0
  N1_at_p0 : N1.eval p0 = 0
  N2_at_p0 : N2.eval p0 = 0
  N2_at_p1 : N2.eval p1 = 0
  N0_at_p0_ne_zero : N0.eval p0 ≠ 0
  N1_at_p1_ne_zero : N1.eval p1 ≠ 0
  N2_at_z_ne_zero : N2.eval z ≠ 0
  F_ne_zero : F ≠ 0

theorem transferPolynomial_eval (F K P : Polynomial R) (ξ t : R) :
    (transferPolynomial F K ξ P).eval t =
      F.eval t * P.eval t + P.eval ξ * K.eval t := by
  simp [transferPolynomial]

theorem transferPolynomial_eval_xi (F K P : Polynomial R) (ξ : R) :
    (transferPolynomial F K ξ P).eval ξ =
      P.eval ξ * (F.eval ξ + K.eval ξ) := by
  rw [transferPolynomial_eval]
  ring

theorem transferPolynomial_of_eval_zero (F K P : Polynomial R) (ξ : R)
    (hP : P.eval ξ = 0) :
    transferPolynomial F K ξ P = F * P := by
  simp [transferPolynomial, hP]

theorem transferPolynomial_sub (F K P Q : Polynomial R) (ξ : R) :
    transferPolynomial F K ξ (P - Q) =
      transferPolynomial F K ξ P - transferPolynomial F K ξ Q := by
  simp only [transferPolynomial, Polynomial.eval_sub, Polynomial.C_sub]
  ring

/-- The old polynomial is recovered from its transfer without any
assumption about the three additional columns. -/
theorem transferPolynomial_zero_iff [IsDomain R] (F K P : Polynomial R) (ξ : R)
    (hF : F ≠ 0) (hpivot : F.eval ξ + K.eval ξ ≠ 0) :
    transferPolynomial F K ξ P = 0 ↔ P = 0 := by
  constructor
  · intro hzero
    have heval := congrArg (fun Q : Polynomial R => Q.eval ξ) hzero
    have hprod : P.eval ξ * (F.eval ξ + K.eval ξ) = 0 := by
      simpa only [transferPolynomial_eval_xi, Polynomial.eval_zero] using heval
    have hPxi : P.eval ξ = 0 := (mul_eq_zero.mp hprod).resolve_right hpivot
    rw [transferPolynomial_of_eval_zero F K P ξ hPxi] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hF
  · rintro rfl
    simp [transferPolynomial]

theorem transferPolynomial_injective [IsDomain R] (F K : Polynomial R) (ξ : R)
    (hF : F ≠ 0) (hpivot : F.eval ξ + K.eval ξ ≠ 0) :
    Function.Injective (transferPolynomial F K ξ) := by
  intro P Q heq
  apply sub_eq_zero.mp
  apply (transferPolynomial_zero_iff F K (P - Q) ξ hF hpivot).mp
  rw [transferPolynomial_sub, heq, sub_self]

theorem extensionPolynomial_sub (F K N0 N1 N2 : Polynomial R) (ξ : R)
    (x y w x' y' w' : R) (P Q : Polynomial R) :
    extensionPolynomial F K N0 N1 N2 ξ (x - x') (y - y') (w - w') (P - Q) =
      extensionPolynomial F K N0 N1 N2 ξ x y w P -
        extensionPolynomial F K N0 N1 N2 ξ x' y' w' Q := by
  simp only [extensionPolynomial, Polynomial.C_sub, transferPolynomial_sub]
  ring

/-- Evaluation at ξ, p0, p1 and z successively kills P(ξ), x, y and w.
The remaining relation is F*P=0, and F is nonzero. -/
theorem extensionPolynomial_zero_iff [IsDomain R]
    {F K N0 N1 N2 : Polynomial R} {ξ p0 p1 z : R}
    (h : SeparationConditions F K N0 N1 N2 ξ p0 p1 z)
    (x y w : R) (P : Polynomial R) :
    extensionPolynomial F K N0 N1 N2 ξ x y w P = 0 ↔
      x = 0 ∧ y = 0 ∧ w = 0 ∧ P = 0 := by
  constructor
  · intro hzero
    have hevalxi := congrArg (fun Q : Polynomial R => Q.eval ξ) hzero
    have hprod : P.eval ξ * (F.eval ξ + K.eval ξ) = 0 := by
      simpa [extensionPolynomial, transferPolynomial_eval_xi,
        h.N0_at_xi, h.N1_at_xi, h.N2_at_xi] using hevalxi
    have hPxi : P.eval ξ = 0 :=
      (mul_eq_zero.mp hprod).resolve_right h.pivot_ne_zero
    have hevalp0 := congrArg (fun Q : Polynomial R => Q.eval p0) hzero
    have hxprod : x * N0.eval p0 = 0 := by
      simpa [extensionPolynomial, transferPolynomial, hPxi,
        h.F_at_p0, h.N1_at_p0, h.N2_at_p0] using hevalp0
    have hx : x = 0 :=
      (mul_eq_zero.mp hxprod).resolve_right h.N0_at_p0_ne_zero
    have hevalp1 := congrArg (fun Q : Polynomial R => Q.eval p1) hzero
    have hyprod : y * N1.eval p1 = 0 := by
      simpa [extensionPolynomial, transferPolynomial, hPxi,
        h.F_at_p1, h.N0_at_p1, h.N2_at_p1] using hevalp1
    have hy : y = 0 :=
      (mul_eq_zero.mp hyprod).resolve_right h.N1_at_p1_ne_zero
    have hevalz := congrArg (fun Q : Polynomial R => Q.eval z) hzero
    have hwprod : w * N2.eval z = 0 := by
      simpa [extensionPolynomial, transferPolynomial, hPxi,
        h.F_at_z, hx, hy] using hevalz
    have hw : w = 0 :=
      (mul_eq_zero.mp hwprod).resolve_right h.N2_at_z_ne_zero
    have hFP : F * P = 0 := by
      simpa [extensionPolynomial, transferPolynomial, hPxi, hx, hy, hw] using hzero
    exact ⟨hx, hy, hw, (mul_eq_zero.mp hFP).resolve_left h.F_ne_zero⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp [extensionPolynomial, transferPolynomial]

theorem extensionPolynomial_eq_iff [IsDomain R]
    {F K N0 N1 N2 : Polynomial R} {ξ p0 p1 z : R}
    (h : SeparationConditions F K N0 N1 N2 ξ p0 p1 z)
    (x y w x' y' w' : R) (P Q : Polynomial R) :
    extensionPolynomial F K N0 N1 N2 ξ x y w P =
        extensionPolynomial F K N0 N1 N2 ξ x' y' w' Q ↔
      x = x' ∧ y = y' ∧ w = w' ∧ P = Q := by
  constructor
  · intro heq
    have hzero :
        extensionPolynomial F K N0 N1 N2 ξ (x - x') (y - y') (w - w') (P - Q) =
          0 := by
      rw [extensionPolynomial_sub, heq, sub_self]
    rcases (extensionPolynomial_zero_iff h (x - x') (y - y') (w - w') (P - Q)).mp
      hzero with ⟨hx, hy, hw, hP⟩
    exact ⟨sub_eq_zero.mp hx, sub_eq_zero.mp hy, sub_eq_zero.mp hw, sub_eq_zero.mp hP⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

def combinedExtension (F K N0 N1 N2 : Polynomial R) (ξ : R)
    (input : R × R × R × Polynomial R) : Polynomial R :=
  extensionPolynomial F K N0 N1 N2 ξ input.1 input.2.1 input.2.2.1 input.2.2.2

/-- The three scalar coefficients and the old polynomial are jointly
recoverable under the explicit evaluation conditions. -/
theorem combinedExtension_injective [IsDomain R]
    {F K N0 N1 N2 : Polynomial R} {ξ p0 p1 z : R}
    (h : SeparationConditions F K N0 N1 N2 ξ p0 p1 z) :
    Function.Injective (combinedExtension F K N0 N1 N2 ξ) := by
  rintro ⟨x, y, w, P⟩ ⟨x', y', w', Q⟩ heq
  change extensionPolynomial F K N0 N1 N2 ξ x y w P =
    extensionPolynomial F K N0 N1 N2 ξ x' y' w' Q at heq
  rcases (extensionPolynomial_eq_iff h x y w x' y' w' P Q).mp heq with
    ⟨rfl, rfl, rfl, rfl⟩
  rfl

end

end PanelMoments.SourceInvariantTailPolynomialExtension

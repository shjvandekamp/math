import PanelMoments.SourcePolynomialKernels

set_option autoImplicit false

/-!
# Output-coordinate factors of the actual cleared source columns

Every cleared kernel entry in output column `c` contains `X c`. Left
multiplication preserves this factor, so every nonempty ordered kernel
product has the same property. The canonical empty and singleton words
are nonempty by construction. Their delta terms also contain the required
coordinate, either from the leading coordinate or the shared kernel.

Consequently every component of the actual cleared source and reduced
families is `X c` times a polynomial. These are polynomial identities for
arbitrary coefficient tables; no positivity or independence assumption
is needed.
-/

namespace PanelMoments.SourceCoordinateFactors

open scoped BigOperators
open SourcePolynomialKernels SourceTransferOrders SourceNewIndices

noncomputable section

theorem dvd_matrix_mul_entry (p : Poly) (M K : Matrix (State 2) (State 2) Poly)
    (a c : State 2) (h : ∀ b, p ∣ K b c) : p ∣ (M * K) a c := by
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum (fun b _ => dvd_mul_of_dvd_right (h b) (M a b))

theorem clearedKernel_dvd_output (A : Table 2) (t : ℕ) (a c : State 2) :
    MvPolynomial.X c ∣ clearedKernel A t a c := by
  refine ⟨MvPolynomial.C (A t a c) *
    ∏ b ∈ Finset.univ.erase a, rowPolynomial A t b, ?_⟩
  change MvPolynomial.C (A t a c) * MvPolynomial.X c *
      (∏ b ∈ Finset.univ.erase a, rowPolynomial A t b) = _
  ring

/-- Nonempty actual words retain the output-coordinate factor of their last kernel. -/
theorem clearedWordProduct_dvd_output {N : ℕ} (A : Table 2) (w : List (Fin N))
    (hw : w ≠ []) (a c : State 2) :
    MvPolynomial.X c ∣ clearedWordProduct A w a c := by
  induction w generalizing a with
  | nil => exact (hw rfl).elim
  | cons u w ih =>
      cases w with
      | nil => simpa [clearedWordProduct] using clearedKernel_dvd_output A (u.val + 2) a c
      | cons v w =>
          change MvPolynomial.X c ∣
            (clearedKernel A (u.val + 2) * clearedWordProduct A (v :: w)) a c
          exact dvd_matrix_mul_entry _ _ _ a c (fun b => ih (by simp) b)

theorem clearedEmptyVector_dvd_output {N : ℕ} (A : Table 2) (s : Fin N) (a c : State 2) :
    MvPolynomial.X c ∣ clearedEmptyVector A s a c := by
  by_cases hac : a = c
  · subst c
    exact dvd_mul_right _ _
  · have hw := clearedWordProduct_dvd_output A (emptyWord s) (by simp [emptyWord]) a c
    simp only [clearedEmptyVector, hac, ite_false, mul_zero, zero_sub]
    exact dvd_mul_of_dvd_right (dvd_neg.mpr hw) _

theorem clearedSingletonVector_dvd_output {N : ℕ} (A : Table 2) (t : Fin N)
    (s : {s : Fin N // s ≠ t}) (a b c : State 2) :
    MvPolynomial.X c ∣ clearedSingletonVector A t s a b c := by
  by_cases hbc : b = c
  · subst c
    exact dvd_mul_of_dvd_left
      (dvd_mul_of_dvd_right (clearedKernel_dvd_output A (t.val + 2) a b) (MvPolynomial.X a)) _
  · have hw := clearedWordProduct_dvd_output A (singletonWord t s.val)
      (by simp [singletonWord]) b c
    simp only [clearedSingletonVector, hbc, ite_false, mul_zero, zero_sub]
    exact dvd_mul_of_dvd_right (dvd_neg.mpr hw) _

theorem clearedSingleBlockVector_dvd_output {N : ℕ} (A : Table 2) (s : Fin N)
    (a c : State 2) : MvPolynomial.X c ∣ clearedSingleBlockVector A s a c := by
  by_cases hac : a = c
  · subst c
    exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _
  · simp only [clearedSingleBlockVector, hac, ite_false, mul_zero, zero_sub]
    exact dvd_mul_of_dvd_right (dvd_neg.mpr (clearedKernel_dvd_output A (s.val + 2) a c)) _

theorem clearedSourceColumn_dvd_output {N : ℕ} (A : Table 2) (p : NewParameter N)
    (c : State 2) : MvPolynomial.X c ∣ clearedSourceColumn A p c := by
  cases p with
  | inl p => exact clearedEmptyVector_dvd_output A p.1 p.2 c
  | inr p => exact clearedSingletonVector_dvd_output A p.1 p.2.1 p.2.2.2 p.2.2.1 c

theorem clearedReducedColumn_dvd_output {N : ℕ} (A : Table 2) (p : NewParameter N)
    (c : State 2) : MvPolynomial.X c ∣ clearedReducedColumn A p c := by
  cases p with
  | inl p => exact clearedSingleBlockVector_dvd_output A p.1 p.2 c
  | inr p => exact clearedSingletonVector_dvd_output A p.1 p.2.1 p.2.2.2 p.2.2.1 c

/-- A polynomial quotient of the actual cleared source component by its output coordinate. -/
def sourceComponentQuotient {N : ℕ} (A : Table 2) (p : NewParameter N) (c : State 2) : Poly :=
  Classical.choose (dvd_def.mp (clearedSourceColumn_dvd_output A p c))

def reducedComponentQuotient {N : ℕ} (A : Table 2) (p : NewParameter N) (c : State 2) : Poly :=
  Classical.choose (dvd_def.mp (clearedReducedColumn_dvd_output A p c))

theorem clearedSourceColumn_eq_coordinate_mul {N : ℕ} (A : Table 2) (p : NewParameter N)
    (c : State 2) :
    clearedSourceColumn A p c = MvPolynomial.X c * sourceComponentQuotient A p c :=
  Classical.choose_spec (dvd_def.mp (clearedSourceColumn_dvd_output A p c))

theorem clearedReducedColumn_eq_coordinate_mul {N : ℕ} (A : Table 2) (p : NewParameter N)
    (c : State 2) :
    clearedReducedColumn A p c = MvPolynomial.X c * reducedComponentQuotient A p c :=
  Classical.choose_spec (dvd_def.mp (clearedReducedColumn_dvd_output A p c))

end

end PanelMoments.SourceCoordinateFactors

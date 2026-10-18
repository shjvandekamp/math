import PanelMoments.SourceLocalJetAlgebra

set_option autoImplicit false

/-!
# The first mixed-pair coefficient of the actual cleared special jet

`clearedSpecial` is the actual special jet multiplied by `L_a² L_b²`
where those row forms are nonzero. Its explicit numerator is defined
everywhere, including a point where both row forms vanish.

Along `X(ε) = P + ε Y`, its derivative at such a point depends only on
the tail's value at zero. The tail may be any entrywise differentiable
matrix curve; its derivatives cancel from the first numerator coefficient.
The final corollary supplies this differentiability for the actual ordered
kernel tail when its row denominators are nonzero at the pair point.
This is an exact cleared-numerator statement, without a residue operator,
nonvanishing assertion, or rank conclusion.
-/

namespace PanelMoments.SourceMixedPoleJet

open scoped BigOperators
open SourceHomogeneous SourceRelativeTimeJet SourceLocalJetAlgebra

noncomputable section

def clearedSpecial {n : ℕ} (A : Table n) (X : State n → ℝ) (t : ℕ)
    (d : State n → ℝ) (Q : Matrix (State n) (State n) ℝ)
    (a b j : State n) : ℝ :=
  prefixNumerator A X t a b *
    (d b * (if b = j then 1 else 0) * rowForm A X t a * rowForm A X t b ^ 2 -
     rowFormJet A X t d a * (if b = j then 1 else 0) * rowForm A X t b ^ 2 +
     rowDirectionTail A X t d Q b j * rowForm A X t a * rowForm A X t b +
     rowFormJet A X t d a * rowTail A X t Q b j * rowForm A X t b -
     rowFormJet A X t d b * rowTail A X t Q b j * rowForm A X t a)

/-- The numerator is connected to the existing actual kernel jet. -/
theorem denominator_mul_specialJet {n : ℕ} (A : Table n) (X : State n → ℝ)
    (t : ℕ) (d : State n → ℝ) (Q : Matrix (State n) (State n) ℝ)
    (a b j : State n) (hLa : rowForm A X t a ≠ 0) (hLb : rowForm A X t b ≠ 0) :
    rowForm A X t a ^ 2 * rowForm A X t b ^ 2 * specialJet A X t d Q a b j =
      clearedSpecial A X t d Q a b j := by
  rw [specialJet_expansion A X t d Q a b j hLa hLb]
  unfold clearedSpecial
  field_simp [hLa, hLb]

theorem clearedSpecial_eq_zero_of_pair {n : ℕ} (A : Table n) (P : State n → ℝ)
    (t : ℕ) (d : State n → ℝ) (Q : Matrix (State n) (State n) ℝ)
    (a b j : State n) (hPa : rowForm A P t a = 0) (hPb : rowForm A P t b = 0) :
    clearedSpecial A P t d Q a b j = 0 := by
  simp [clearedSpecial, hPa, hPb]

def affinePoint {n : ℕ} (P Y : State n → ℝ) (ε : ℝ) : State n → ℝ :=
  fun k => P k + ε * Y k

@[simp] theorem affinePoint_zero {n : ℕ} (P Y : State n → ℝ) :
    affinePoint P Y 0 = P := by
  funext k
  simp [affinePoint]

private theorem affinePoint_hasDerivAt {n : ℕ} (P Y : State n → ℝ) (k : State n) :
    HasDerivAt (fun ε : ℝ => affinePoint P Y ε k) (Y k) 0 := by
  simpa [affinePoint] using ((hasDerivAt_id (0 : ℝ)).mul_const (Y k)).const_add (P k)

theorem rowForm_affine_hasDerivAt {n : ℕ} (A : Table n) (P Y : State n → ℝ)
    (t : ℕ) (a : State n) :
    HasDerivAt (fun ε : ℝ => rowForm A (affinePoint P Y ε) t a)
      (rowForm A Y t a) 0 := by
  unfold rowForm
  exact HasDerivAt.fun_sum (fun k _ =>
    (affinePoint_hasDerivAt P Y k).const_mul (A t a k))

/-- An actual kernel entry is differentiable along an affine coordinate curve
whenever its row denominator is nonzero at the base point. -/
theorem kernel_affine_differentiableAt {n : ℕ} (A : Table n) (P Y : State n → ℝ)
    (t : ℕ) (a b : State n) (hL : rowForm A P t a ≠ 0) :
    DifferentiableAt ℝ (fun ε : ℝ => kernel A (affinePoint P Y ε) t a b) 0 := by
  exact (((affinePoint_hasDerivAt P Y b).const_mul (A t a b)).fun_div
    (rowForm_affine_hasDerivAt A P Y t a)
    (by simpa only [affinePoint_zero] using hL)).differentiableAt

/-- Entrywise differentiability of the existing ordered product, with its
actual time indices `u.val + 2`; no order or distinctness hypothesis is needed. -/
theorem homogeneousWordProduct_affine_differentiableAt {N : ℕ} (A : Table 2)
    (P Y : State 2 → ℝ) (w : List (Fin N))
    (hL : ∀ u ∈ w, ∀ a, rowForm A P (u.val + 2) a ≠ 0) (a b : State 2) :
    DifferentiableAt ℝ
      (fun ε : ℝ => homogeneousWordProduct A (affinePoint P Y ε) w a b) 0 := by
  revert hL a b
  induction w with
  | nil =>
      intro _ a b
      simpa only [homogeneousWordProduct, List.map_nil, List.prod_nil] using
        (differentiableAt_const ((1 : Matrix (State 2) (State 2) ℝ) a b))
  | cons u w ih =>
      intro hL a b
      have hHead : rowForm A P (u.val + 2) a ≠ 0 := hL u (by simp) a
      have hTail : ∀ v ∈ w, ∀ c, rowForm A P (v.val + 2) c ≠ 0 := by
        intro v hv c
        exact hL v (by simp [hv]) c
      simpa only [homogeneousWordProduct, List.map_cons, List.prod_cons,
        Matrix.mul_apply] using
        (DifferentiableAt.fun_sum (fun k _ =>
          (kernel_affine_differentiableAt A P Y (u.val + 2) a k hHead).fun_mul
            (ih hTail k b)))

/-- The exact first numerator coefficient at a pair of row-form zeros.
No derivative of the tail remains, although the tail is allowed to vary. -/
theorem clearedSpecial_affine_hasDerivAt {n : ℕ} (A : Table n) (P Y : State n → ℝ)
    (t : ℕ) (d : State n → ℝ)
    (Q : ℝ → Matrix (State n) (State n) ℝ) (a b j : State n)
    (hPa : rowForm A P t a = 0) (hPb : rowForm A P t b = 0)
    (hQ : ∀ k l, DifferentiableAt ℝ (fun ε : ℝ => Q ε k l) 0) :
    HasDerivAt (fun ε : ℝ => clearedSpecial A (affinePoint P Y ε) t d (Q ε) a b j)
      (prefixNumerator A P t a b * rowTail A P t (Q 0) b j *
        (rowFormJet A P t d a * rowForm A Y t b -
          rowFormJet A P t d b * rowForm A Y t a)) 0 := by
  have hX (k : State n) := (affinePoint_hasDerivAt P Y k).differentiableAt
  have hN : DifferentiableAt ℝ
      (fun ε : ℝ => prefixNumerator A (affinePoint P Y ε) t a b) 0 := by
    unfold prefixNumerator
    exact ((hX a).const_mul (A t a b)).fun_mul (hX b)
  have hE (c : State n) : DifferentiableAt ℝ
      (fun ε : ℝ => rowFormJet A (affinePoint P Y ε) t d c) 0 := by
    unfold rowFormJet
    exact DifferentiableAt.fun_sum (fun k _ =>
      ((hX k).const_mul (A t c k)).mul_const (d k))
  have hS : DifferentiableAt ℝ
      (fun ε : ℝ => rowTail A (affinePoint P Y ε) t (Q ε) b j) 0 := by
    unfold rowTail
    exact DifferentiableAt.fun_sum (fun k _ =>
      ((hX k).const_mul (A t b k)).fun_mul (hQ k j))
  have hD : DifferentiableAt ℝ
      (fun ε : ℝ => rowDirectionTail A (affinePoint P Y ε) t d (Q ε) b j) 0 := by
    unfold rowDirectionTail
    exact DifferentiableAt.fun_sum (fun k _ =>
      (((hX k).const_mul (A t b k)).mul_const (d k - d b)).fun_mul (hQ k j))
  have hLa := rowForm_affine_hasDerivAt A P Y t a
  have hLb := rowForm_affine_hasDerivAt A P Y t b
  have hOne := (hLa.const_mul (d b * (if b = j then 1 else 0))).fun_mul
    (hLb.fun_mul hLb)
  have hTwo := ((hE a).hasDerivAt.mul_const (if b = j then 1 else 0)).fun_mul
    (hLb.fun_mul hLb)
  have hThree := (hD.hasDerivAt.fun_mul hLa).fun_mul hLb
  have hFour := ((hE a).hasDerivAt.fun_mul hS.hasDerivAt).fun_mul hLb
  have hFive := ((hE b).hasDerivAt.fun_mul hS.hasDerivAt).fun_mul hLa
  have hTotal := hN.hasDerivAt.fun_mul
    ((((hOne.fun_sub hTwo).fun_add hThree).fun_add hFour).fun_sub hFive)
  convert hTotal using 1
  · funext ε
    simp only [clearedSpecial, pow_two]
  · simp only [affinePoint_zero, hPa, hPb, mul_zero, zero_mul, add_zero, zero_add,
      sub_zero]
    ring

/-- The mixed-pair coefficient with the actual ordered model-kernel tail.
The generic differentiability hypothesis is discharged by the tail's row-form
units at `P`, while the two row forms belonging to the special jet vanish. -/
theorem clearedSpecial_word_affine_hasDerivAt {N : ℕ} (A : Table 2)
    (P Y : State 2 → ℝ) (t : ℕ) (d : State 2 → ℝ) (w : List (Fin N))
    (a b j : State 2) (hPa : rowForm A P t a = 0) (hPb : rowForm A P t b = 0)
    (hL : ∀ u ∈ w, ∀ c, rowForm A P (u.val + 2) c ≠ 0) :
    HasDerivAt (fun ε : ℝ => clearedSpecial A (affinePoint P Y ε) t d
      (homogeneousWordProduct A (affinePoint P Y ε) w) a b j)
      (prefixNumerator A P t a b * rowTail A P t (homogeneousWordProduct A P w) b j *
        (rowFormJet A P t d a * rowForm A Y t b -
          rowFormJet A P t d b * rowForm A Y t a)) 0 := by
  simpa only [affinePoint_zero] using
    (clearedSpecial_affine_hasDerivAt A P Y t d
      (fun ε : ℝ => homogeneousWordProduct A (affinePoint P Y ε) w) a b j hPa hPb
      (fun k l => homogeneousWordProduct_affine_differentiableAt A P Y w hL k l))

end

end PanelMoments.SourceMixedPoleJet

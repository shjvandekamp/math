import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Universal algebra for the auxiliary binary transfer construction

These are identities over an arbitrary field. The evaluation variable `z` is
kept explicit, as are all assumptions needed to divide. The prefix definitions
are the actual ordered weighted sums, not abstract variables constrained by the
desired conclusions.

The module proves the parity recurrence and the two outer-peeling identities.
It does not assert a Laurent basis rank, independence of source moments, or a
finite-span parity theorem for functions of `z`.
-/

namespace PanelMoments.BinaryTransferAlgebra

variable {K : Type*} [Field K]

def H (ρ c z : K) : K :=
  (1 + c * z) * (1 + ρ * c * z) / ((ρ - 1) * c * z)

def Q (ρ c z : K) : K := (1 + ρ * c * z) / (ρ - 1)

def R (ρ c z : K) : K := (1 + c * z) / ((ρ - 1) * c)

theorem H_eq_one_add_Q_add_R (ρ c z : K) (hρ : ρ ≠ 1) (hc : c ≠ 0) (hz : z ≠ 0) :
    H ρ c z = 1 + Q ρ c z + R ρ c z / z := by
  unfold H Q R
  field_simp [sub_ne_zero.mpr hρ, hc, hz]
  ring

/-- The ordered sum `Σᵢ Q(cᵢ,z) ∏ⱼ<ᵢ H(cⱼ,z)`. -/
def prefixQ (ρ : K) : List K → K → K
  | [], _ => 0
  | c :: cs, z => Q ρ c z + H ρ c z * prefixQ ρ cs z

/-- The corresponding ordered weighted sum of `R`. -/
def prefixR (ρ : K) : List K → K → K
  | [], _ => 0
  | c :: cs, z => R ρ c z + H ρ c z * prefixR ρ cs z

/-- Product of the transfer factors in the prefix. -/
def prefixH (ρ : K) : List K → K → K
  | [], _ => 1
  | c :: cs, z => H ρ c z * prefixH ρ cs z

@[simp] theorem prefixQ_nil (ρ z : K) : prefixQ ρ [] z = 0 := rfl
@[simp] theorem prefixR_nil (ρ z : K) : prefixR ρ [] z = 0 := rfl
@[simp] theorem prefixH_nil (ρ z : K) : prefixH ρ [] z = 1 := rfl

@[simp] theorem prefixQ_singleton (ρ c z : K) : prefixQ ρ [c] z = Q ρ c z := by
  simp [prefixQ]

@[simp] theorem prefixR_singleton (ρ c z : K) : prefixR ρ [c] z = R ρ c z := by
  simp [prefixR]

@[simp] theorem prefixH_singleton (ρ c z : K) : prefixH ρ [c] z = H ρ c z := by
  simp [prefixH]

theorem prefixQ_append (ρ z : K) (cs ds : List K) :
    prefixQ ρ (cs ++ ds) z = prefixQ ρ cs z + prefixH ρ cs z * prefixQ ρ ds z := by
  induction cs with
  | nil => simp [prefixQ, prefixH]
  | cons c cs ih =>
    simp only [List.cons_append, prefixQ, prefixH, ih]
    ring

theorem prefixR_append (ρ z : K) (cs ds : List K) :
    prefixR ρ (cs ++ ds) z = prefixR ρ cs z + prefixH ρ cs z * prefixR ρ ds z := by
  induction cs with
  | nil => simp [prefixR, prefixH]
  | cons c cs ih =>
    simp only [List.cons_append, prefixR, prefixH, ih]
    ring

theorem prefixH_append (ρ z : K) (cs ds : List K) :
    prefixH ρ (cs ++ ds) z = prefixH ρ cs z * prefixH ρ ds z := by
  induction cs with
  | nil => simp [prefixH]
  | cons c cs ih =>
    simp only [List.cons_append, prefixH, ih]
    ring

theorem prefixH_eq_one_add_prefixQ_add_prefixR (ρ z : K) (cs : List K)
    (hρ : ρ ≠ 1) (hz : z ≠ 0) (hcs : ∀ c ∈ cs, c ≠ 0) :
    prefixH ρ cs z = 1 + prefixQ ρ cs z + prefixR ρ cs z / z := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hc : c ≠ 0 := hcs c (by simp)
    have htail : ∀ d ∈ cs, d ≠ 0 := fun d hd => hcs d (by simp [hd])
    simp only [prefixH, prefixQ, prefixR]
    rw [ih htail, H_eq_one_add_Q_add_R ρ c z hρ hc hz]
    ring

/-- The scalar defect when the newly appended factor is moved to the front. -/
def moveDefect (ρ U V c z : K) : K := (R ρ c z * U - Q ρ c z * V) / z

def appendQ (ρ U V c z : K) : K := U + (1 + U + V / z) * Q ρ c z

def appendR (ρ U V c z : K) : K := V + (1 + U + V / z) * R ρ c z

def moveFirst (ρ : K) (cs : List K) (c z : K) : K :=
  moveDefect ρ (prefixQ ρ cs z) (prefixR ρ cs z) c z

theorem move_Q_identity (ρ U V c z : K) (hρ : ρ ≠ 1) (hc : c ≠ 0) (hz : z ≠ 0) :
    Q ρ c z + H ρ c z * U - appendQ ρ U V c z = moveDefect ρ U V c z := by
  rw [H_eq_one_add_Q_add_R ρ c z hρ hc hz]
  unfold appendQ moveDefect
  ring

theorem move_R_identity (ρ U V c z : K) (hρ : ρ ≠ 1) (hc : c ≠ 0) (hz : z ≠ 0) :
    R ρ c z + H ρ c z * V - appendR ρ U V c z = -z * moveDefect ρ U V c z := by
  rw [H_eq_one_add_Q_add_R ρ c z hρ hc hz]
  unfold appendR moveDefect
  field_simp [hz]
  ring

theorem prefixQ_moveFirst (ρ z c : K) (cs : List K)
    (hρ : ρ ≠ 1) (hc : c ≠ 0) (hz : z ≠ 0) (hcs : ∀ d ∈ cs, d ≠ 0) :
    prefixQ ρ (c :: cs) z - prefixQ ρ (cs ++ [c]) z = moveFirst ρ cs c z := by
  rw [prefixQ_append, prefixQ_singleton,
    prefixH_eq_one_add_prefixQ_add_prefixR ρ z cs hρ hz hcs]
  exact move_Q_identity ρ (prefixQ ρ cs z) (prefixR ρ cs z) c z hρ hc hz

theorem prefixR_moveFirst (ρ z c : K) (cs : List K)
    (hρ : ρ ≠ 1) (hc : c ≠ 0) (hz : z ≠ 0) (hcs : ∀ d ∈ cs, d ≠ 0) :
    prefixR ρ (c :: cs) z - prefixR ρ (cs ++ [c]) z = -z * moveFirst ρ cs c z := by
  rw [prefixR_append, prefixR_singleton,
    prefixH_eq_one_add_prefixQ_add_prefixR ρ z cs hρ hz hcs]
  exact move_R_identity ρ (prefixQ ρ cs z) (prefixR ρ cs z) c z hρ hc hz

def F (ρ V c z : K) : K := -(1 + ρ * c * z) * V / z

def prefixF (ρ : K) (cs : List K) (c z : K) : K := F ρ (prefixR ρ cs z) c z

@[simp] theorem prefixF_nil (ρ c z : K) : prefixF ρ [] c z = 0 := by
  simp [prefixF, F]

@[simp] theorem moveFirst_nil (ρ c z : K) : moveFirst ρ [] c z = 0 := by
  simp [moveFirst, moveDefect]

/-- Universal parity step, before substituting any actual prefix. -/
theorem F_append_identity (ρ U V e c z : K) (hρ : ρ ≠ 1)
    (he : e ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0) (hec : e ≠ c) :
    F ρ (appendR ρ U V e z) c z = 1 - F ρ V e z +
      (ρ - 1) / (e - c) * (e * moveDefect ρ U V e z -
        c * moveDefect ρ (appendQ ρ U V e z) (appendR ρ U V e z) c z) := by
  unfold F appendQ appendR moveDefect Q R
  field_simp [sub_ne_zero.mpr hρ, he, hc, hz, sub_ne_zero.mpr hec]
  ring

/-- The parity recurrence for the actual ordered prefix sums. -/
theorem prefixF_append (ρ z e c : K) (cs : List K) (hρ : ρ ≠ 1)
    (he : e ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0) (hec : e ≠ c)
    (hcs : ∀ d ∈ cs, d ≠ 0) :
    prefixF ρ (cs ++ [e]) c z = 1 - prefixF ρ cs e z +
      (ρ - 1) / (e - c) * (e * moveFirst ρ cs e z - c * moveFirst ρ (cs ++ [e]) c z) := by
  simp only [prefixF, moveFirst, prefixQ_append, prefixR_append,
    prefixQ_singleton, prefixR_singleton]
  rw [prefixH_eq_one_add_prefixQ_add_prefixR ρ z cs hρ hz hcs]
  exact F_append_identity ρ (prefixQ ρ cs z) (prefixR ρ cs z) e c z hρ he hc hz hec

theorem prefixF_singleton (ρ e c z : K) (hρ : ρ ≠ 1)
    (he : e ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0) (hec : e ≠ c) :
    prefixF ρ [e] c z = 1 - ((ρ - 1) / (e - c) * c) * moveFirst ρ [e] c z := by
  have h := prefixF_append ρ z e c [] hρ he hc hz hec (by simp)
  simpa only [List.nil_append, prefixF_nil, moveFirst_nil, mul_zero, sub_zero,
    zero_sub, mul_neg, sub_eq_add_neg, mul_assoc, neg_zero, zero_add, add_zero] using h

/-- Scalar remaining after the two outer transfer factors are peeled off. -/
def outerS (ρ U V c d z : K) : K :=
  (d * (1 + ρ * c * z) * V - (1 + c * z) * U) / ((c - d) * z)

theorem outer_peel_Q (ρ U V c d z : K) (hρ : ρ ≠ 1)
    (hc : c ≠ 0) (hd : d ≠ 0) (hz : z ≠ 0) (hcd : c ≠ d) :
    (U + (1 + U + V / z) * (Q ρ c z + H ρ c z * Q ρ d z)) -
      (d * (1 + ρ * c * z) / (c - d)) *
        moveDefect ρ (appendQ ρ U V c z) (appendR ρ U V c z) d z =
      Q ρ d z * outerS ρ U V c d z := by
  unfold appendQ appendR moveDefect outerS H Q R
  field_simp [sub_ne_zero.mpr hρ, hc, hd, hz, sub_ne_zero.mpr hcd]
  ring

theorem outer_peel_R (ρ U V c d z : K) (hρ : ρ ≠ 1)
    (hc : c ≠ 0) (hd : d ≠ 0) (hz : z ≠ 0) (hcd : c ≠ d) :
    (V + (1 + U + V / z) * (R ρ c z + H ρ c z * R ρ d z)) -
      ((1 + c * z) / (c - d)) *
        moveDefect ρ (appendQ ρ U V c z) (appendR ρ U V c z) d z =
      R ρ d z * outerS ρ U V c d z := by
  unfold appendQ appendR moveDefect outerS H Q R
  field_simp [sub_ne_zero.mpr hρ, hc, hd, hz, sub_ne_zero.mpr hcd]
  ring

theorem outerS_eq_F_sub_moveDefect (ρ U V c d z : K) (hρ : ρ ≠ 1)
    (hc : c ≠ 0) (hz : z ≠ 0) (hcd : c ≠ d) :
    outerS ρ U V c d z = F ρ V c z -
      (c * (ρ - 1) / (c - d)) * moveDefect ρ U V c z := by
  unfold outerS F moveDefect Q R
  field_simp [sub_ne_zero.mpr hρ, hc, hz, sub_ne_zero.mpr hcd]
  ring

end PanelMoments.BinaryTransferAlgebra

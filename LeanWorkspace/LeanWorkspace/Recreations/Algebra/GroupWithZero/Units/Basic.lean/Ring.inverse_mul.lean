import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

theorem Ring.inverse_mul {a b : M₀} (h : IsUnit a ∨ IsUnit b) : (a * b)⁻¹ʳ = b⁻¹ʳ * a⁻¹ʳ := by
  obtain (⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩) :
      (IsUnit a ∧ ¬ IsUnit b) ∨ (¬ IsUnit a ∧ IsUnit b) ∨ (IsUnit a ∧ IsUnit b) := by grind
  · have : ¬ IsUnit (a * b) := by simpa [ha.mul_left_iff]
    simp [Ring.inverse_non_unit, hb, this]
  · have : ¬ IsUnit (a * b) := by simpa [hb.mul_right_iff]
    simp [Ring.inverse_non_unit, ha, this]
  · simp [Ring.inverse_of_isUnit, ha, hb, ha.mul hb, ← Units.val_mul, ← mul_inv_rev]
    simp


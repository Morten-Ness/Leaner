import Mathlib

open scoped Ring

variable {R : Type*}

theorem Ring.inverse_sub_inverse [Ring R] {a b : R} (h : IsUnit a ↔ IsUnit b) :
    a⁻¹ʳ - b⁻¹ʳ = a⁻¹ʳ * (b - a) * b⁻¹ʳ := by
  by_cases ha : IsUnit a
  · have hb := h.mp ha
    obtain ⟨ia⟩ := ha.nonempty_invertible
    obtain ⟨ib⟩ := hb.nonempty_invertible
    simp_rw [inverse_invertible, invOf_sub_invOf]
  · have hb := h.not.mp ha
    simp [inverse_non_unit, ha, hb]


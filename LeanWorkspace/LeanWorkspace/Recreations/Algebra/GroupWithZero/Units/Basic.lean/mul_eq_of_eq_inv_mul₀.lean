import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem mul_eq_of_eq_inv_mul₀ (hb : b ≠ 0) (h : b = a⁻¹ * c) : a * b = c := by
  rwa [← eq_inv_mul_iff_mul_eq₀]; rintro rfl; simp [hb] at h


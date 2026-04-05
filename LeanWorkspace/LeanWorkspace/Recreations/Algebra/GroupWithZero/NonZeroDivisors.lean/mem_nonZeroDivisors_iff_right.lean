import Mathlib

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem mem_nonZeroDivisors_iff_right : r ∈ M₀⁰ ↔ ∀ x, x * r = 0 → x = 0 := by
  rw [← nonZeroDivisorsRight_eq_nonZeroDivisors]; rfl


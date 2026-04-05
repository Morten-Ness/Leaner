import Mathlib

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem mem_nonZeroDivisors_iff_left : r ∈ M₀⁰ ↔ ∀ x, r * x = 0 → x = 0 := by
  rw [← nonZeroDivisorsLeft_eq_nonZeroDivisors]; rfl


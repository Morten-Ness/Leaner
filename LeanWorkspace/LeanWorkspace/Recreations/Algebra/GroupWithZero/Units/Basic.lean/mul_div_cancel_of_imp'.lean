import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem mul_div_cancel_of_imp' (h : b = 0 → a = 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel_of_imp h]


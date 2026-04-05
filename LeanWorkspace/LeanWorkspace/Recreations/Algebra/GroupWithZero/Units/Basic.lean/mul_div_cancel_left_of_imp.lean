import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [CommGroupWithZero G₀] {a b c d : G₀}

theorem mul_div_cancel_left_of_imp (h : a = 0 → b = 0) : a * b / a = b := by
  rw [mul_comm, mul_div_cancel_of_imp h]


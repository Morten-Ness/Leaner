import Mathlib

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem nonZeroDivisorsRight_eq_left : nonZeroDivisorsRight M₀ = nonZeroDivisorsLeft M₀ := by
  rw [nonZeroDivisorsLeft_eq_right]


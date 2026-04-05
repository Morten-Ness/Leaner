import Mathlib

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem nonZeroDivisorsRight_eq_nonZeroDivisors : nonZeroDivisorsRight M₀ = nonZeroDivisors M₀ := by
  rw [← nonZeroDivisorsLeft_eq_right, nonZeroDivisorsLeft_eq_nonZeroDivisors]


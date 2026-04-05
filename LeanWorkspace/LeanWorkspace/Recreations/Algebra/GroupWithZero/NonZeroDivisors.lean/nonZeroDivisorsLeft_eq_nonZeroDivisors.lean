import Mathlib

variable {M₀ : Type*} [CommMonoidWithZero M₀] {a b r x : M₀}

theorem nonZeroDivisorsLeft_eq_nonZeroDivisors : nonZeroDivisorsLeft M₀ = nonZeroDivisors M₀ := by
  rw [nonZeroDivisors, nonZeroDivisorsLeft_eq_right, inf_idem]


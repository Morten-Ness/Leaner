import Mathlib

variable (M₀ : Type*) [MonoidWithZero M₀] {x : M₀}

theorem nonZeroDivisorsLeft_eq_right (M₀ : Type*) [CommMonoidWithZero M₀] :
    nonZeroDivisorsLeft M₀ = nonZeroDivisorsRight M₀ := by
  ext x; simp [mul_comm x]


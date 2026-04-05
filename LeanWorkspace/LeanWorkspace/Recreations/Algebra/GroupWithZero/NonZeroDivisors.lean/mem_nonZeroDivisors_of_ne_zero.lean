import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

variable [NoZeroDivisors M₀]

theorem mem_nonZeroDivisors_of_ne_zero (hx : x ≠ 0) : x ∈ M₀⁰ := ⟨fun _ ↦ eq_zero_of_ne_zero_of_mul_left_eq_zero hx,
   fun _ ↦ eq_zero_of_ne_zero_of_mul_right_eq_zero hx⟩


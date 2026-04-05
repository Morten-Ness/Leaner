import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem noZeroDivisors_iff_forall_mem_nonZeroDivisorsLeft :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → x ∈ nonZeroDivisorsLeft M₀ := noZeroDivisors_iff_right_eq_zero_of_mul


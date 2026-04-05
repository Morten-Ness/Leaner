import Mathlib

variable {F M₀ M₀' : Type*} [MonoidWithZero M₀] [MonoidWithZero M₀'] {r x y : M₀}

theorem noZeroDivisors_iff_forall_mem_nonZeroDivisorsRight :
    NoZeroDivisors M₀ ↔ ∀ x : M₀, x ≠ 0 → x ∈ nonZeroDivisorsRight M₀ := noZeroDivisors_iff_left_eq_zero_of_mul


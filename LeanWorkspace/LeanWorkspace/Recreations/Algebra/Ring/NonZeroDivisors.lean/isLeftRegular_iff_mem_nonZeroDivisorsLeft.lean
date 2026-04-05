import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem isLeftRegular_iff_mem_nonZeroDivisorsLeft : IsLeftRegular r ↔ r ∈ nonZeroDivisorsLeft R := isLeftRegular_iff_right_eq_zero_of_mul


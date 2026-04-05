import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem isRightRegular_iff_mem_nonZeroDivisorsRight : IsRightRegular r ↔ r ∈ nonZeroDivisorsRight R := isRightRegular_iff_left_eq_zero_of_mul


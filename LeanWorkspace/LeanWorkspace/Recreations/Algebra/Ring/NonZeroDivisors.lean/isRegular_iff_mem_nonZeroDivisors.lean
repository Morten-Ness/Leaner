import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem isRegular_iff_mem_nonZeroDivisors : IsRegular r ↔ r ∈ R⁰ := isRegular_iff_eq_zero_of_mul


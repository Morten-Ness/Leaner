import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem isUnit_iff_mem_nonZeroDivisors_of_finite [Finite R] : IsUnit a ↔ a ∈ nonZeroDivisors R := by
  rw [← isRegular_iff_mem_nonZeroDivisors, isRegular_iff_isUnit_of_finite]


import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem mul_cancel_left_mem_nonZeroDivisorsLeft (hr : r ∈ nonZeroDivisorsLeft R) :
    r * x = r * y ↔ x = y := ⟨(isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr hr ·), congr_arg (r * ·)⟩


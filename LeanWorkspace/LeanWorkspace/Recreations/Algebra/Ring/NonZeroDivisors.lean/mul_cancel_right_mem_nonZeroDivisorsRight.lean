import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem mul_cancel_right_mem_nonZeroDivisorsRight (hr : r ∈ nonZeroDivisorsRight R) :
    x * r = y * r ↔ x = y := ⟨(isRightRegular_iff_mem_nonZeroDivisorsRight.mpr hr ·), congr_arg (· * r)⟩


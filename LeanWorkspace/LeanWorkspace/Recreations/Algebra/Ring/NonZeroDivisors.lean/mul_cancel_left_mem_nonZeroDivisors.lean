import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem mul_cancel_left_mem_nonZeroDivisors (hr : r ∈ R⁰) : r * x = r * y ↔ x = y := mul_cancel_left_mem_nonZeroDivisorsLeft hr.1


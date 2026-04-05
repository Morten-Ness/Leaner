import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem mul_cancel_right_mem_nonZeroDivisors (hr : r ∈ R⁰) : x * r = y * r ↔ x = y := mul_cancel_right_mem_nonZeroDivisorsRight hr.2


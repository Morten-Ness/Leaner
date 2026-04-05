import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem mul_cancel_left_coe_nonZeroDivisors {c : R⁰} : (c : R) * x = c * y ↔ x = y := mul_cancel_left_mem_nonZeroDivisors c.prop


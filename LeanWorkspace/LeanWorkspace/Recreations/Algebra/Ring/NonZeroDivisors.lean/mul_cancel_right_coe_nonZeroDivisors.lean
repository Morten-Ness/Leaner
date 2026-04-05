import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem mul_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c = y * c ↔ x = y := mul_cancel_right_mem_nonZeroDivisors c.prop


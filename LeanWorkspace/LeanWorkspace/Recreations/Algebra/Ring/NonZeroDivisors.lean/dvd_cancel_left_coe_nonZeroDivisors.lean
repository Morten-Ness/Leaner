import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem dvd_cancel_left_coe_nonZeroDivisors {c : R⁰} : c * x ∣ c * y ↔ x ∣ y := dvd_cancel_left_mem_nonZeroDivisors c.prop


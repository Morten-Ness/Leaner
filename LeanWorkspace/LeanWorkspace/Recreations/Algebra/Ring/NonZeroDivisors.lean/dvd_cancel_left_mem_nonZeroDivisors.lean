import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [Ring R] {a x y r : R}

theorem dvd_cancel_left_mem_nonZeroDivisors (hr : r ∈ R⁰) : r * x ∣ r * y ↔ x ∣ y := (isLeftRegular_iff_mem_nonZeroDivisorsLeft.mpr hr.1).dvd_cancel_left


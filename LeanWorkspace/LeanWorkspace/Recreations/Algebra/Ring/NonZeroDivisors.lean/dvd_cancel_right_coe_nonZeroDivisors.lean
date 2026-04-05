import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] {r x y : R}

theorem dvd_cancel_right_coe_nonZeroDivisors {c : R⁰} : x * c ∣ y * c ↔ x ∣ y := dvd_cancel_right_mem_nonZeroDivisors c.prop


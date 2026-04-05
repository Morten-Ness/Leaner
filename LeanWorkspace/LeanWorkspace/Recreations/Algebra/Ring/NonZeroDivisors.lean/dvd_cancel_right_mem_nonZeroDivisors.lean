import Mathlib

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] {r x y : R}

theorem dvd_cancel_right_mem_nonZeroDivisors (hr : r ∈ R⁰) : x * r ∣ y * r ↔ x ∣ y := by
  simp_rw [← mul_comm r, dvd_cancel_left_mem_nonZeroDivisors hr]


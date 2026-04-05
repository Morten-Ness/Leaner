import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem reverse_eq_zero : f.reverse = 0 ↔ f = 0 := by simp [Polynomial.reverse]


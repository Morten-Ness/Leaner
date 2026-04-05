import Mathlib

open scoped Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

theorem revAt_zero (N : ℕ) : Polynomial.revAt N 0 = N := by simp


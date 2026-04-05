import Mathlib

variable {R : Type*} [Semiring R]

theorem toFn_zero (n : ℕ) : Polynomial.toFn n (0 : R[X]) = 0 := by simp


import Mathlib

variable {R : Type*} [Semiring R] [DecidableEq R]

theorem ofFn_zero (n : ℕ) : Polynomial.ofFn n (0 : Fin n → R) = 0 := by simp


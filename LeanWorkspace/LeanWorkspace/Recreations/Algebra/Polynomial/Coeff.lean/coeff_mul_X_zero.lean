import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_mul_X_zero (p : R[X]) : coeff (p * Polynomial.X) 0 = 0 := by simp


import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_X_mul_zero (p : R[X]) : coeff (Polynomial.X * p) 0 = 0 := by simp


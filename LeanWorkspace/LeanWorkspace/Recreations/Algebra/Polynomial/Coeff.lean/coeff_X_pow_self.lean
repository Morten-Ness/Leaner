import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem coeff_X_pow_self (n : ℕ) : coeff (Polynomial.X ^ n : R[X]) n = 1 := by simp


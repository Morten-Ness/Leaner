import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem mul_coeff_zero (p q : R[X]) : coeff (p * q) 0 = coeff p 0 * coeff q 0 := by simp [Polynomial.coeff_mul]


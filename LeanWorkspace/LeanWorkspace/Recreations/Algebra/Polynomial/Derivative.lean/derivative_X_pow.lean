import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_X_pow (n : ℕ) : Polynomial.derivative (Polynomial.X ^ n : R[X]) = Polynomial.C (n : R) * Polynomial.X ^ (n - 1) := by
  convert Polynomial.derivative_C_mul_X_pow (1 : R) n <;> simp


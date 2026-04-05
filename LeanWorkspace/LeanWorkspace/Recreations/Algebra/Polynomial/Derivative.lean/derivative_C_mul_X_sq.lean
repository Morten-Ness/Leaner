import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_C_mul_X_sq (a : R) : Polynomial.derivative (Polynomial.C a * Polynomial.X ^ 2) = Polynomial.C (a * 2) * Polynomial.X := by
  rw [Polynomial.derivative_C_mul_X_pow, Nat.cast_two, pow_one]


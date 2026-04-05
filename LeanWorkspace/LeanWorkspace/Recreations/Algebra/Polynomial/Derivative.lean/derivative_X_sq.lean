import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_X_sq : Polynomial.derivative (Polynomial.X ^ 2 : R[X]) = Polynomial.C 2 * Polynomial.X := by
  rw [Polynomial.derivative_X_pow, Nat.cast_two, pow_one]


import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_X_pow_succ (n : ℕ) :
    Polynomial.derivative (Polynomial.X ^ (n + 1) : R[X]) = Polynomial.C (n + 1 : R) * Polynomial.X ^ n := by
  simp [Polynomial.derivative_X_pow]


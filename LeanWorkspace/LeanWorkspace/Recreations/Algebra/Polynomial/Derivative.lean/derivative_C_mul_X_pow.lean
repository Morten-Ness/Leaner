import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_C_mul_X_pow (a : R) (n : ℕ) :
    Polynomial.derivative (Polynomial.C a * Polynomial.X ^ n) = Polynomial.C (a * n) * Polynomial.X ^ (n - 1) := by
  rw [C_mul_X_pow_eq_monomial, C_mul_X_pow_eq_monomial, Polynomial.derivative_monomial]


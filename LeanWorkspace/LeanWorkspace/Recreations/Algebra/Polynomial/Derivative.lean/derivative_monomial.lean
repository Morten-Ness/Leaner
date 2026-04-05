import Mathlib

open scoped Nat

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem derivative_monomial (a : R) (n : ℕ) :
    Polynomial.derivative (monomial n a) = monomial (n - 1) (a * n) := by
  rw [Polynomial.derivative_apply, sum_monomial_index, C_mul_X_pow_eq_monomial]
  simp


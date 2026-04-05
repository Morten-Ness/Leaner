import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem C_mul_X_pow_eq_monomial : ∀ {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = Polynomial.monomial n a
  | 0 => mul_one _
  | n + 1 => by
    rw [pow_succ, ← mul_assoc, C_mul_X_pow_eq_monomial, Polynomial.X, Polynomial.monomial_mul_monomial, mul_one]

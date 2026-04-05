import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem smul_X_eq_monomial {n} : a • Polynomial.X ^ n = Polynomial.monomial n (a : R) := by
  rw [Polynomial.X_pow_eq_monomial, Polynomial.smul_monomial, smul_eq_mul, mul_one]


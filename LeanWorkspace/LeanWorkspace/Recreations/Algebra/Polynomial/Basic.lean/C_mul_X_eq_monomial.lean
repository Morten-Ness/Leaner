import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem C_mul_X_eq_monomial : Polynomial.C a * Polynomial.X = Polynomial.monomial 1 a := by rw [← Polynomial.C_mul_X_pow_eq_monomial, pow_one]


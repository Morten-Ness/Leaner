import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_C_mul_X (a : R) : (Polynomial.C a * Polynomial.X).toFinsupp = .single 1 a := by
  rw [Polynomial.C_mul_X_eq_monomial, Polynomial.toFinsupp_monomial]


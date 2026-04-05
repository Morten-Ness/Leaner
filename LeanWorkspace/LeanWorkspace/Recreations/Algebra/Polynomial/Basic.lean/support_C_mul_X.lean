import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_C_mul_X {c : R} (h : c ≠ 0) : Polynomial.support (Polynomial.C c * Polynomial.X) = singleton 1 := by
  rw [Polynomial.C_mul_X_eq_monomial, Polynomial.support_monomial 1 h]


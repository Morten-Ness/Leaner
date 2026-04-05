import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_C_mul_X_pow (n : ℕ) {c : R} (h : c ≠ 0) :
    Polynomial.support (Polynomial.C c * Polynomial.X ^ n) = singleton n := by
  rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.support_monomial n h]


import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_C_mul_X_pow' (n : ℕ) (c : R) : Polynomial.support (Polynomial.C c * Polynomial.X ^ n) ⊆ singleton n := by
  simpa only [Polynomial.C_mul_X_pow_eq_monomial] using Polynomial.support_monomial' n c


import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeffs_monomial (n : ℕ) {c : R} (hc : c ≠ 0) : (Polynomial.monomial n c).coeffs = {c} := by
  rw [Polynomial.coeffs, Polynomial.support_monomial n hc]
  simp


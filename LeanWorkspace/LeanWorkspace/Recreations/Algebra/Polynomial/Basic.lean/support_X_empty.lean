import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_X_empty (H : (1 : R) = 0) : (Polynomial.X : R[X]).support = ∅ := by
  rw [Polynomial.X, H, Polynomial.monomial_zero_right, Polynomial.support_zero]


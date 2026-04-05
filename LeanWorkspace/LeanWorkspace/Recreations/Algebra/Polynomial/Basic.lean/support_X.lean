import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_X (H : ¬(1 : R) = 0) : (Polynomial.X : R[X]).support = singleton 1 := by
  rw [← pow_one Polynomial.X, Polynomial.support_X_pow H 1]


import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_update_zero (p : R[X]) (n : ℕ) : Polynomial.support (p.update n 0) = p.support.erase n := by
  rw [Polynomial.update_zero_eq_erase, Polynomial.support_erase]


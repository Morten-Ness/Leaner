import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem update_zero_eq_erase (p : R[X]) (n : ℕ) : p.update n 0 = p.erase n := by
  ext
  rw [Polynomial.coeff_update_apply, Polynomial.coeff_erase]


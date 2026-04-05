import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem erase_ne (p : R[X]) (n i : ℕ) (h : i ≠ n) : Polynomial.coeff (p.erase n) i = Polynomial.coeff p i := by
  simp [Polynomial.coeff_erase, h]


import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem erase_same (p : R[X]) (n : ℕ) : Polynomial.coeff (p.erase n) n = 0 := by simp [Polynomial.coeff_erase]


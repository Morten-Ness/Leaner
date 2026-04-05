import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_erase (p : R[X]) (n : ℕ) : toFinsupp (p.erase n) = p.toFinsupp.erase n := by
  simp only [erase_def]


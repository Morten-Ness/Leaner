import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_toFinsupp (p : R[X]) : p.toFinsupp.support = p.support := by rw [Polynomial.support]


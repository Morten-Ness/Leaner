import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_add (a b : R[X]) : (a + b).toFinsupp = a.toFinsupp + b.toFinsupp := (rfl)


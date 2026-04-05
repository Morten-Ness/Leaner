import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_apply (f : R[X]) (i) : f.toFinsupp i = f.coeff i := by cases f; rfl


import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_neg {R : Type u} [Ring R] (a : R[X]) : (-a).toFinsupp = -a.toFinsupp := (rfl)


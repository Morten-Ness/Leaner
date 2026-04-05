import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_zero : (0 : R[X]).toFinsupp = 0 := rfl


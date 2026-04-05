import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_one : (1 : R[X]).toFinsupp = 1 := rfl


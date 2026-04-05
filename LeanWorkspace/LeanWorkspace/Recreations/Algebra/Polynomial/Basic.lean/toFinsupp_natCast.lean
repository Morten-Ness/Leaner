import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem toFinsupp_natCast (n : ℕ) : (n : R[X]).toFinsupp = n := rfl


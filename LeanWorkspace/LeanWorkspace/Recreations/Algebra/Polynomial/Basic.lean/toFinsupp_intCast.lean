import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Ring R]

theorem toFinsupp_intCast (z : ℤ) : (z : R[X]).toFinsupp = z := rfl


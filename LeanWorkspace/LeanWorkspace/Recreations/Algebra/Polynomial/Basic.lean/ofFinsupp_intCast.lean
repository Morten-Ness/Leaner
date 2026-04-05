import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Ring R]

theorem ofFinsupp_intCast (z : ℤ) : (⟨z⟩ : R[X]) = z := rfl


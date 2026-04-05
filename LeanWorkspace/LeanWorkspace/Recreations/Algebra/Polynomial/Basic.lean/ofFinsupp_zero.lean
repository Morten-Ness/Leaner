import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ofFinsupp_zero : (⟨0⟩ : R[X]) = 0 := rfl


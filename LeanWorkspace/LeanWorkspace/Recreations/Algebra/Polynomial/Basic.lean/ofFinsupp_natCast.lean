import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ofFinsupp_natCast (n : ℕ) : (⟨n⟩ : R[X]) = n := rfl


import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ofFinsupp_ofNat (n : ℕ) [n.AtLeastTwo] : (⟨ofNat(n)⟩ : R[X]) = ofNat(n) := rfl


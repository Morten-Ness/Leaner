import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ofFinsupp_neg {R : Type u} [Ring R] {a} : (⟨-a⟩ : R[X]) = -⟨a⟩ := (rfl)


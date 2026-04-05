import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem ofFinsupp_mul (a b) : (⟨a * b⟩ : R[X]) = ⟨a⟩ * ⟨b⟩ := (rfl)


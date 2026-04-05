import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_ofFinsupp (p) : Polynomial.support (⟨p⟩ : R[X]) = p.support := by rw [Polynomial.support]


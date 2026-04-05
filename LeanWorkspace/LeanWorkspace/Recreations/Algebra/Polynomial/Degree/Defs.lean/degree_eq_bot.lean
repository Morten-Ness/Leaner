import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem degree_eq_bot : Polynomial.degree p = ⊥ ↔ p = 0 := ⟨fun h => support_eq_empty.1 (Finset.max_eq_bot.1 h), fun h => h.symm ▸ rfl⟩


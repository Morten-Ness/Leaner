import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem card_support_eq_zero : #p.support = 0 ↔ p = 0 := by simp


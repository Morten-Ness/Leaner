import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem notMem_support_iff : n ∉ p.support ↔ p.coeff n = 0 := by simp


import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem mem_support_iff : n ∈ p.support ↔ p.coeff n ≠ 0 := by
  rcases p with ⟨⟩
  simp


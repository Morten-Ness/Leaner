import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

set_option backward.isDefEq.respectTransparency false in
theorem support_eq_empty : p.support = ∅ ↔ p = 0 := by
  rcases p with ⟨⟩
  simp [Polynomial.support]


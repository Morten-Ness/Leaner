import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem support_add : (p + q).support ⊆ p.support ∪ q.support := by
  simpa [Polynomial.support] using Finsupp.support_add


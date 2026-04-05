import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q : R[X]}

theorem coeffs_nonempty_iff {p : R[X]} : p.coeffs.Nonempty ↔ p ≠ 0 := by
  simp [Finset.nonempty_iff_ne_empty]


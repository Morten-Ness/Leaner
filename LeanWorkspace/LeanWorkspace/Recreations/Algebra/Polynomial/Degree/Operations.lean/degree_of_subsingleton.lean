import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem degree_of_subsingleton [Subsingleton R] : degree p = ⊥ := by
  rw [Subsingleton.elim p 0, degree_zero]


import Mathlib

variable {R : Type u} {S : Type v} {a b c d : R} {n m : ℕ}

variable [Semiring R] [Semiring S] {p q r : R[X]}

theorem natDegree_of_subsingleton [Subsingleton R] : natDegree p = 0 := by
  rw [Subsingleton.elim p 0, natDegree_zero]


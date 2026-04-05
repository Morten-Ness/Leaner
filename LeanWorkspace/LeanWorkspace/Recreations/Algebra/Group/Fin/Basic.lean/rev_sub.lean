import Mathlib

variable {n : ℕ}

theorem rev_sub (a b : Fin n) : rev (a - b) = rev a + b := by
  rw [rev_eq_iff, Fin.rev_add, rev_rev]


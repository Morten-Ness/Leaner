import Mathlib

variable {n : ℕ}

theorem add_lt_left_iff {n : ℕ} {a b : Fin n} : a + b < a ↔ rev b < a := by
  rw [← rev_lt_rev, Iff.comm, ← rev_lt_rev, Fin.rev_add, Fin.lt_sub_iff, rev_rev]


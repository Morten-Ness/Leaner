import Mathlib

variable {n : ℕ}

theorem lt_sub_one_iff {k : Fin (n + 2)} : k < k - 1 ↔ k = 0 := by
  simp


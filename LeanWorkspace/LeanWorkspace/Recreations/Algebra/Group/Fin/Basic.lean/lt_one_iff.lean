import Mathlib

variable {n : ℕ}

theorem lt_one_iff {n : ℕ} (x : Fin (n + 2)) : x < 1 ↔ x = 0 := by
  simp [lt_def]


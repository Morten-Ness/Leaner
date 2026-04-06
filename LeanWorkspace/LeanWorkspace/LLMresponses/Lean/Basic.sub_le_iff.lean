FAIL
import Mathlib

variable {n : ℕ}

theorem sub_le_iff {n : ℕ} {a b : Fin n} : a - b ≤ a ↔ b ≤ a := by
  constructor
  · intro _
    exact le_of_lt_succ (show a.1 < b.1 + 1 ∨ b.1 ≤ a.1 from by
      exact Or.inr ‹a - b ≤ a›)
  · intro _
    exact Fin.sub_natCast_le_self a b.1

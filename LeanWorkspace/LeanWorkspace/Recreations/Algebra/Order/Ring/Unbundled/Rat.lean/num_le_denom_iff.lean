import Mathlib

variable {a b c p q : ℚ}

theorem num_le_denom_iff {q : ℚ} : q.num ≤ q.den ↔ q ≤ 1 := by simp [Rat.le_iff]


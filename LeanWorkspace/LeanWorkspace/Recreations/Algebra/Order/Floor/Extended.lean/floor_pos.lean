import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem floor_pos : 0 < ⌊r⌋ₑ ↔ 1 ≤ r := by simp


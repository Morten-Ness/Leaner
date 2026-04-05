import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem ceil_pos : 0 < ⌈r⌉ₑ ↔ 0 < r := by simp


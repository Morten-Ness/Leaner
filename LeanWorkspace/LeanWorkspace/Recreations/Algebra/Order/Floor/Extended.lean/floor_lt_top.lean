import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem floor_lt_top : ⌊r⌋ₑ < ⊤ ↔ r < ∞ := by cases r <;> simp


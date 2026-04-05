import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem ceil_lt_add_one (hr : r ≠ ∞) : (⌈r⌉ₑ : ℝ≥0∞) < r + 1 := by
  lift r to ℝ≥0 using hr; simpa using mod_cast Nat.ceil_lt_add_one (zero_le r)


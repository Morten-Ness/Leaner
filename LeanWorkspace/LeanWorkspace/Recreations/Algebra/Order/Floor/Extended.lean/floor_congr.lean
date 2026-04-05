import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem floor_congr (h : ∀ n : ℕ∞, n ≤ r ↔ n ≤ s) : ⌊r⌋ₑ = ⌊s⌋ₑ := eq_of_forall_le_iff <| by simpa


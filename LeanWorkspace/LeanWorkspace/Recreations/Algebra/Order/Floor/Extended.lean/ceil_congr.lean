import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem ceil_congr (h : ∀ n : ℕ∞, r ≤ n ↔ s ≤ n) : ⌈r⌉ₑ = ⌈s⌉ₑ := eq_of_forall_ge_iff <| by simpa


import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem ceil_mono : Monotone (ceil : ℝ≥0∞ → ℕ∞) := fun r s hrs ↦ by simpa using hrs.trans le_ceil_self


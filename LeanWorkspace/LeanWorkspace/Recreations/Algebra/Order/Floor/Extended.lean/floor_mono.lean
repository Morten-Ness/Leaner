import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem floor_mono : Monotone (floor : ℝ≥0∞ → ℕ∞) := fun r s hrs ↦ by simpa using hrs.trans' floor_le_self


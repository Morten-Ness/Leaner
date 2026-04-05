import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem gc_ceil_toENNReal : GaloisConnection ceil (↑) := fun _ _ ↦ ceil_le


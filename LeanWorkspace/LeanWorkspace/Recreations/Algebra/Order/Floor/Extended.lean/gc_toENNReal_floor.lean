import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem gc_toENNReal_floor : GaloisConnection (↑) floor := fun _ _ ↦ le_floor.symm


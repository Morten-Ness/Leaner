import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem floor_sub_ofNat (r : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] : ⌊r - ofNat(n)⌋ₑ = ⌊r⌋ₑ - ofNat(n) := floor_sub_toENNReal r n


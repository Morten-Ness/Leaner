import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem ceil_add_ofNat (r : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] : ⌈r + ofNat(n)⌉ₑ = ⌈r⌉ₑ + ofNat(n) := ceil_add_natCast r n


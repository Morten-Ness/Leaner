import Mathlib

open scoped ENNReal NNReal

variable {r s : ℝ≥0∞} {n : ℕ∞}

theorem ceil_add_le : ∀ (r s : ℝ≥0∞), ⌈r + s⌉ₑ ≤ ⌈r⌉ₑ + ⌈s⌉ₑ
  | ∞, _ => by simp
  | _, ∞ => by simp
  | (r : ℝ≥0), (s : ℝ≥0) => mod_cast Nat.ceil_add_le r s

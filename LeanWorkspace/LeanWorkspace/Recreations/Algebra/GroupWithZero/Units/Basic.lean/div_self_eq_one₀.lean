import Mathlib

open scoped Ring

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀] {a b c : G₀} {m n : ℕ}

theorem div_self_eq_one₀ : a / a = 1 ↔ a ≠ 0 where
  mp := by contrapose!; simp +contextual
  mpr := div_self


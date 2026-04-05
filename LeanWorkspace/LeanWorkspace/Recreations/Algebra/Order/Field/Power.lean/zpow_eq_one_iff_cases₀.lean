import Mathlib

variable {α : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} {n : ℤ}

theorem zpow_eq_one_iff_cases₀ : a ^ n = 1 ↔ n = 0 ∨ a = 1 ∨ a = -1 ∧ Even n := by
  simp [← zpow_eq_zpow_iff_cases₀]


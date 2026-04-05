import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : ℕ}

variable [ZeroLEOneClass M₀]

theorem pow_le_one_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : a ^ n ≤ 1 ↔ a ≤ 1 := by
  refine ⟨fun h ↦ ?_, pow_le_one₀ ha⟩
  contrapose! h
  exact one_lt_pow₀ h hn


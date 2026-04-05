import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : ℕ}

variable [ZeroLEOneClass M₀]

theorem one_le_pow_iff_of_nonneg (ha : 0 ≤ a) (hn : n ≠ 0) : 1 ≤ a ^ n ↔ 1 ≤ a := by
  refine ⟨fun h ↦ ?_, fun h ↦ one_le_pow₀ h⟩
  contrapose! h
  exact pow_lt_one₀ ha h hn


import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [LinearOrder M₀] [PosMulStrictMono M₀] {a b : M₀}
  {m n : ℕ}

variable [ZeroLEOneClass M₀]

theorem pow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Function.Injective (a ^ ·) := by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (pow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (pow_right_strictMono₀ ha₁).injective


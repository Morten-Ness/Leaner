import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [LinearOrder G₀] {a b c d : G₀}

variable {m n : ℤ}

variable [PosMulStrictMono G₀]

variable [ZeroLEOneClass G₀]

theorem zpow_right_injective₀ (ha₀ : 0 < a) (ha₁ : a ≠ 1) : Function.Injective fun n : ℤ ↦ a ^ n := by
  obtain ha₁ | ha₁ := ha₁.lt_or_gt
  · exact (zpow_right_strictAnti₀ ha₀ ha₁).injective
  · exact (zpow_right_strictMono₀ ha₁).injective


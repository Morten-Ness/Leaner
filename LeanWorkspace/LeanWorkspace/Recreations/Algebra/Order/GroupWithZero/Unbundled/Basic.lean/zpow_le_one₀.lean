import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [ZeroLEOneClass G₀]

variable {m n : ℤ}

theorem zpow_le_one₀ (ha₀ : 0 < a) (ha₁ : a ≤ 1) (hn : 0 ≤ n) : a ^ n ≤ 1 := by
  simpa using zpow_right_anti₀ ha₀ ha₁ hn


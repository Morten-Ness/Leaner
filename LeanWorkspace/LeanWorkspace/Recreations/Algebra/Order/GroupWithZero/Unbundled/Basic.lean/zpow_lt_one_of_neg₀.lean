import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [ZeroLEOneClass G₀]

variable {m n : ℤ}

theorem zpow_lt_one_of_neg₀ (ha : 1 < a) (hn : n < 0) : a ^ n < 1 := by
  simpa using zpow_right_strictMono₀ ha hn


import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [ZeroLEOneClass G₀]

variable {m n : ℤ}

theorem one_le_zpow₀ (ha : 1 ≤ a) (hn : 0 ≤ n) : 1 ≤ a ^ n := by simpa using zpow_right_mono₀ ha hn


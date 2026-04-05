import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [ZeroLEOneClass G₀]

variable {m n : ℤ}

theorem zpow_le_zpow_right₀ (ha : 1 ≤ a) (hmn : m ≤ n) : a ^ m ≤ a ^ n := zpow_right_mono₀ ha hmn


import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [ZeroLEOneClass G₀]

variable {m n : ℤ}

theorem zpow_lt_zpow_right_of_lt_one₀ (ha₀ : 0 < a) (ha₁ : a < 1) (hmn : m < n) : a ^ n < a ^ m := zpow_right_strictAnti₀ ha₀ ha₁ hmn


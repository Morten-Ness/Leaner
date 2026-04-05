import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [PartialOrder G₀]

variable [PosMulReflectLT G₀] {a b c : G₀}

variable [MulPosMono G₀] {n : ℤ}

theorem zpow_le_zpow_left₀ (hn : 0 ≤ n) (ha : 0 ≤ a) (h : a ≤ b) : a ^ n ≤ b ^ n := zpow_left_monoOn₀ (G₀ := G₀) hn ha (by grind) h


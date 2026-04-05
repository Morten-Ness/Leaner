import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [LinearOrder G₀] {a b c d : G₀}

variable {m n : ℤ}

variable [PosMulReflectLT G₀] [MulPosMono G₀]

theorem zpow_le_zpow_iff_left₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 < n) : a ^ n ≤ b ^ n ↔ a ≤ b := (zpow_left_strictMonoOn₀ (G₀ := G₀) hn).le_iff_le ha hb


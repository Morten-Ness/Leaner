import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [GroupWithZero G₀]

variable [LinearOrder G₀] {a b c d : G₀}

variable {m n : ℤ}

variable [PosMulStrictMono G₀] [MulPosMono G₀]

theorem zpow_left_inj₀ (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : n ≠ 0) :
    a ^ n = b ^ n ↔ a = b := (zpow_left_injOn₀ hn).eq_iff ha hb


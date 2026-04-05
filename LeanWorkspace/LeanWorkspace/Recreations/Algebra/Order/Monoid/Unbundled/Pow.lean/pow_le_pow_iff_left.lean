import Mathlib

variable {β G M : Type*}

variable [Monoid M]

variable [LinearOrder M]

variable [MulLeftStrictMono M] [MulRightStrictMono M]

theorem pow_le_pow_iff_left {a b : M} {n : ℕ} (hn : n ≠ 0) : a ^ n ≤ b ^ n ↔ a ≤ b := (pow_left_strictMono hn).le_iff_le


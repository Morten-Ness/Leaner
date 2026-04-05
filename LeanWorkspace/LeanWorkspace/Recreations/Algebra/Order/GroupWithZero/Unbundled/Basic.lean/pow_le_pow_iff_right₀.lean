import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

variable [PosMulStrictMono M₀]

variable [ZeroLEOneClass M₀]

theorem pow_le_pow_iff_right₀ (h : 1 < a) : a ^ n ≤ a ^ m ↔ n ≤ m := (pow_right_strictMono₀ h).le_iff_le


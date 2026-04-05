import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

variable [PosMulStrictMono M₀]

variable [ZeroLEOneClass M₀]

theorem pow_lt_pow_right₀ (h : 1 < a) (hmn : m < n) : a ^ m < a ^ n := pow_right_strictMono₀ h hmn


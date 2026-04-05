import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

theorem lt_mul_self [ZeroLEOneClass M₀] [MulPosStrictMono M₀] (ha : 1 < a) : a < a * a := lt_mul_left (ha.trans_le' zero_le_one) ha


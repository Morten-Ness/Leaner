import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem one_lt_mul_of_le_of_lt [ZeroLEOneClass M₀] [MulPosMono M₀] (ha : 1 ≤ a) (hb : 1 < b) :
    1 < a * b := hb.trans_le <| le_mul_of_one_le_left (zero_le_one.trans hb.le) ha


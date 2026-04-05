import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem one_lt_mul_of_lt_of_le [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 < a) (hb : 1 ≤ b) :
    1 < a * b := ha.trans_le <| le_mul_of_one_le_right (zero_le_one.trans ha.le) hb

alias one_lt_mul := one_lt_mul_of_le_of_lt


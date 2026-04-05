import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀] (ha : 1 ≤ a) (hmn : m ≤ n) :
    a ^ m ≤ a ^ n := pow_right_mono₀ ha hmn


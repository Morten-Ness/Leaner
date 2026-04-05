import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem mul_lt_one_of_nonneg_of_lt_one_right [MulPosMono M₀] (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b < 1) :
    a * b < 1 := (mul_le_of_le_one_left hb₀ ha).trans_lt hb


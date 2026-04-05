import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem mul_le_one₀ [MulPosMono M₀] (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 := (mul_le_mul_of_nonneg_right ha hb₀).trans <| by rwa [one_mul]


import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem pow_le_one₀ [PosMulMono M₀] {n : ℕ} (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) : a ^ n ≤ 1 := pow_zero a ▸ pow_right_anti₀ ha₀ ha₁ (Nat.zero_le n)


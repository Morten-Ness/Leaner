import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem pow_le_pow_of_le_one [PosMulMono M₀] (ha₀ : 0 ≤ a) (ha₁ : a ≤ 1) {m n : ℕ}
    (hmn : m ≤ n) : a ^ n ≤ a ^ m := pow_right_anti₀ ha₀ ha₁ hmn


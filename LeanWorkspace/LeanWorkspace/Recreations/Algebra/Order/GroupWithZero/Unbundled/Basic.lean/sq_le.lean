import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem sq_le [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1) : a ^ 2 ≤ a := pow_le_of_le_one h₀ h₁ two_ne_zero


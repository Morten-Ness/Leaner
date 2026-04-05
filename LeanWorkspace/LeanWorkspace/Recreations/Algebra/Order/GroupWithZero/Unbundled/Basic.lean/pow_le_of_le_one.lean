import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

theorem pow_le_of_le_one [PosMulMono M₀] (h₀ : 0 ≤ a) (h₁ : a ≤ 1) (hn : n ≠ 0) : a ^ n ≤ a := (pow_one a).subst (pow_le_pow_of_le_one h₀ h₁ (Nat.pos_of_ne_zero hn))


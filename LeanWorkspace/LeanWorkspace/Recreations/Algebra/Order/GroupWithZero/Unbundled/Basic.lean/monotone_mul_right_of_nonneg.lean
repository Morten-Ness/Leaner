import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

variable [Preorder α] {f g : α → M₀}

theorem monotone_mul_right_of_nonneg [MulPosMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ x * a := fun _ _ h ↦ mul_le_mul_of_nonneg_right h ha


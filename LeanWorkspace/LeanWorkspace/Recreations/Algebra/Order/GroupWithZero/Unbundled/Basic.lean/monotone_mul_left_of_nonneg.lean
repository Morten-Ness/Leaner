import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

variable [Preorder α] {f g : α → M₀}

theorem monotone_mul_left_of_nonneg [PosMulMono M₀] (ha : 0 ≤ a) : Monotone fun x ↦ a * x := fun _ _ h ↦ mul_le_mul_of_nonneg_left h ha


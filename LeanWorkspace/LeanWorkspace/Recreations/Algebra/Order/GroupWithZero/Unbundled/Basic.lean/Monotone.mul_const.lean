import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

variable [Preorder α] {f g : α → M₀}

theorem Monotone.mul_const [MulPosMono M₀] (hf : Monotone f) (ha : 0 ≤ a) :
    Monotone fun x ↦ f x * a := (monotone_mul_right_of_nonneg ha).comp hf


import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [Preorder M₀] {a b : M₀} {m n : ℕ}

variable [Preorder α] {f g : α → M₀}

theorem Antitone.mul_const [MulPosMono M₀] (hf : Antitone f) (ha : 0 ≤ a) :
    Antitone fun x ↦ f x * a := (monotone_mul_right_of_nonneg ha).comp_antitone hf


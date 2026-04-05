import Mathlib

variable {α M₀ G₀ : Type*}

variable [Mul M₀] [Zero M₀] [Preorder M₀] [Preorder α] {f g : α → M₀}

theorem Monotone.mul [PosMulMono M₀] [MulPosMono M₀] (hf : Monotone f) (hg : Monotone g)
    (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 ≤ g x) : Monotone (f * g) := fun _ _ h ↦ mul_le_mul (hf h) (hg h) (hg₀ _) (hf₀ _)


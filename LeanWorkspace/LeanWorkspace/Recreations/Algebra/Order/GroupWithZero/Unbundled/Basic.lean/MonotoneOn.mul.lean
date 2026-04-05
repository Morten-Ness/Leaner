import Mathlib

variable {α M₀ G₀ : Type*}

variable [Mul M₀] [Zero M₀] [Preorder M₀] [Preorder α] {f g : α → M₀}

theorem MonotoneOn.mul [PosMulMono M₀] [MulPosMono M₀] {s : Set α} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) (hf₀ : ∀ x ∈ s, 0 ≤ f x) (hg₀ : ∀ x ∈ s, 0 ≤ g x) :
    MonotoneOn (f * g) s := fun _ ha _ hb h ↦ mul_le_mul (hf ha hb h) (hg ha hb h) (hg₀ _ ha) (hf₀ _ hb)


import Mathlib

variable {α M₀ G₀ : Type*}

variable [MonoidWithZero M₀]

variable [PartialOrder M₀] {a b c d : M₀} {m n : ℕ}

variable [Preorder α] {f g : α → M₀}

theorem StrictMono.mul_monotone [PosMulMono M₀] [MulPosStrictMono M₀] (hf : StrictMono f)
    (hg : Monotone g) (hf₀ : ∀ x, 0 ≤ f x) (hg₀ : ∀ x, 0 < g x) :
    StrictMono (f * g) := fun _ _ h ↦ mul_lt_mul (hf h) (hg h.le) (hg₀ _) (hf₀ _)


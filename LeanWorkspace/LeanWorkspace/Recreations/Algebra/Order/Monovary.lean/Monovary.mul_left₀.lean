import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

theorem Monovary.mul_left₀ (hf₁ : 0 ≤ f₁) (hf₂ : 0 ≤ f₂) (h₁ : Monovary f₁ g) (h₂ : Monovary f₂ g) :
    Monovary (f₁ * f₂) g := fun _i _j hij ↦ mul_le_mul (h₁ hij) (h₂ hij) (hf₂ _) (hf₁ _)


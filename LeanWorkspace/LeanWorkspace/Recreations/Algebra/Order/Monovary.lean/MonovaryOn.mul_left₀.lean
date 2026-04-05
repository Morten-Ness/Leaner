import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

theorem MonovaryOn.mul_left₀ (hf₁ : ∀ i ∈ s, 0 ≤ f₁ i) (hf₂ : ∀ i ∈ s, 0 ≤ f₂ i)
    (h₁ : MonovaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) : MonovaryOn (f₁ * f₂) g s := fun _i hi _j hj hij ↦ mul_le_mul (h₁ hi hj hij) (h₂ hi hj hij) (hf₂ _ hi) (hf₁ _ hj)


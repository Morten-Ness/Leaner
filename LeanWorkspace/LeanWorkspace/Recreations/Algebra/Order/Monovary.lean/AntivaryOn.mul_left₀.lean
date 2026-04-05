import Mathlib

variable {ι α β : Type*}

variable [Semiring α] [PartialOrder α] [IsOrderedRing α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

theorem AntivaryOn.mul_left₀ (hf₁ : ∀ i ∈ s, 0 ≤ f₁ i) (hf₂ : ∀ i ∈ s, 0 ≤ f₂ i)
    (h₁ : AntivaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) : AntivaryOn (f₁ * f₂) g s := fun _i hi _j hj hij ↦ mul_le_mul (h₁ hi hj hij) (h₂ hi hj hij) (hf₂ _ hj) (hf₁ _ hi)


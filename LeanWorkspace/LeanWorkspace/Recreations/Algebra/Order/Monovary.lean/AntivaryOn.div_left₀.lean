import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [LinearOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

theorem AntivaryOn.div_left₀ (hf₁ : ∀ i ∈ s, 0 ≤ f₁ i) (hf₂ : ∀ i ∈ s, 0 < f₂ i)
    (h₁ : AntivaryOn f₁ g s) (h₂ : MonovaryOn f₂ g s) : AntivaryOn (f₁ / f₂) g s := fun _i hi _j hj hij ↦ div_le_div₀ (hf₁ _ hi) (h₁ hi hj hij) (hf₂ _ hi) <| h₂ hi hj hij


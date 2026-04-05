import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [LinearOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

theorem MonovaryOn.div_left₀ (hf₁ : ∀ i ∈ s, 0 ≤ f₁ i) (hf₂ : ∀ i ∈ s, 0 < f₂ i)
    (h₁ : MonovaryOn f₁ g s) (h₂ : AntivaryOn f₂ g s) : MonovaryOn (f₁ / f₂) g s := fun _i hi _j hj hij ↦ div_le_div₀ (hf₁ _ hj) (h₁ hi hj hij) (hf₂ _ hj) <| h₂ hi hj hij


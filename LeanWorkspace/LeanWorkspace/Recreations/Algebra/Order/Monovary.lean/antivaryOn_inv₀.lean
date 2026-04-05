import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

theorem antivaryOn_inv₀ (hf : ∀ i ∈ s, 0 < f i) (hg : ∀ i ∈ s, 0 < g i) :
    AntivaryOn f⁻¹ g⁻¹ s ↔ AntivaryOn f g s := by
  rw [antivaryOn_inv_left₀ hf, monovaryOn_inv_right₀ hg]


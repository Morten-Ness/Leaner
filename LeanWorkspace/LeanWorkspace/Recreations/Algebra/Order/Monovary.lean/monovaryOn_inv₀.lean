import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α]
  [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

theorem monovaryOn_inv₀ (hf : ∀ i ∈ s, 0 < f i) (hg : ∀ i ∈ s, 0 < g i) :
    MonovaryOn f⁻¹ g⁻¹ s ↔ MonovaryOn f g s := by
  rw [monovaryOn_inv_left₀ hf, antivaryOn_inv_right₀ hg]


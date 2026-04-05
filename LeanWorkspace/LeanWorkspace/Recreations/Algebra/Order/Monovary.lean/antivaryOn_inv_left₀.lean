import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [LinearOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

theorem antivaryOn_inv_left₀ (hf : ∀ i ∈ s, 0 < f i) : AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s := forall₅_congr fun _i hi _j hj _ ↦ inv_le_inv₀ (hf _ hj) (hf _ hi)


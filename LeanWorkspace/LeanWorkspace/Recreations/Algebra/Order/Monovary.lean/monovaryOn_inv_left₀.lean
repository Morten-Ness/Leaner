import Mathlib

variable {ι α β : Type*}

variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] [LinearOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

theorem monovaryOn_inv_left₀ (hf : ∀ i ∈ s, 0 < f i) : MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s := forall₅_congr fun _i hi _j hj _ ↦ inv_le_inv₀ (hf _ hi) (hf _ hj)


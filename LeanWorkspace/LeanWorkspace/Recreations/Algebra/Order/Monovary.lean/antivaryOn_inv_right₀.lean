import Mathlib

variable {ι α β : Type*}

variable [LinearOrder α] [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

theorem antivaryOn_inv_right₀ (hg : ∀ i ∈ s, 0 < g i) : AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s := forall₂_comm.trans <| forall₄_congr fun i hi j hj ↦ by simp [inv_lt_inv₀ (hg _ hj) (hg _ hi)]


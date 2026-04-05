import Mathlib

variable {ι α β : Type*}

variable [LinearOrder α] [Semifield β] [LinearOrder β] [IsStrictOrderedRing β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g g₁ g₂ : ι → β}

theorem monovaryOn_inv_right₀ (hg : ∀ i ∈ s, 0 < g i) : MonovaryOn f g⁻¹ s ↔ AntivaryOn f g s := forall₂_comm.trans <| forall₄_congr fun i hi j hj ↦ by simp [inv_lt_inv₀ (hg _ hj) (hg _ hi)]


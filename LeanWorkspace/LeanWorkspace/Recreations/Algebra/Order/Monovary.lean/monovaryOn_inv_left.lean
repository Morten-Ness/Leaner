import Mathlib

variable {ι α β : Type*}

variable [CommGroup α] [Preorder α] [IsOrderedMonoid α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

theorem monovaryOn_inv_left : MonovaryOn f⁻¹ g s ↔ AntivaryOn f g s := by
  simp [MonovaryOn, AntivaryOn]


import Mathlib

variable {ι α β : Type*}

variable [CommGroup α] [Preorder α] [IsOrderedMonoid α] [PartialOrder β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

theorem antivaryOn_inv_left : AntivaryOn f⁻¹ g s ↔ MonovaryOn f g s := by
  simp [MonovaryOn, AntivaryOn]


import Mathlib

variable {ι α β : Type*}

variable [PartialOrder α] [CommGroup β] [PartialOrder β] [IsOrderedMonoid β]
  {s : Set ι} {f f₁ f₂ : ι → α} {g : ι → β}

theorem antivaryOn_inv_right : AntivaryOn f g⁻¹ s ↔ MonovaryOn f g s := by
  simpa [MonovaryOn, AntivaryOn] using forall₂_comm


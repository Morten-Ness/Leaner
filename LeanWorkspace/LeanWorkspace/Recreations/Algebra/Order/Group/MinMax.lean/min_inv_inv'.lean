import Mathlib

variable {α : Type*} [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

theorem min_inv_inv' (a b : α) : min a⁻¹ b⁻¹ = (max a b)⁻¹ := Eq.symm <| (@Monotone.map_max α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
    inv_le_inv_iff.mpr


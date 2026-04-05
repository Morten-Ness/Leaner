import Mathlib

variable {α : Type*} [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

theorem max_inv_inv' (a b : α) : max a⁻¹ b⁻¹ = (min a b)⁻¹ := Eq.symm <| (@Monotone.map_min α αᵒᵈ _ _ Inv.inv a b) fun _ _ =>
    inv_le_inv_iff.mpr


import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_inv_Ioo : Inv.inv '' Ioo a b = Ioo (b⁻¹) (a⁻¹) := by simp


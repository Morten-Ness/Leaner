import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_inv_Ici : Inv.inv '' Ici a = Iic (a⁻¹) := by simp


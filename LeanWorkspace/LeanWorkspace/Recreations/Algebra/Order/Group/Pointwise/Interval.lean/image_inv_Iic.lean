import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_inv_Iic : Inv.inv '' Iic a = Ici (a⁻¹) := by simp


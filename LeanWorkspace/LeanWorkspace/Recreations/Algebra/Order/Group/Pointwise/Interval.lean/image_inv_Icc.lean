import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_inv_Icc : Inv.inv '' Icc a b = Icc (b⁻¹) (a⁻¹) := by simp


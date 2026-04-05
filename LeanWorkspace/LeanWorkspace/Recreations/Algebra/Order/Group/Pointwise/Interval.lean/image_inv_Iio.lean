import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_inv_Iio : Inv.inv '' Iio a = Ioi (a⁻¹) := by simp


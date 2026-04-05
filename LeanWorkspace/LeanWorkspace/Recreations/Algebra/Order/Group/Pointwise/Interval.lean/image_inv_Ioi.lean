import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_inv_Ioi : Inv.inv '' Ioi a = Iio (a⁻¹) := by simp


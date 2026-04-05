import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_mul_const_Iic : (fun x => x * a) '' Iic b = Iic (b * a) := by simp


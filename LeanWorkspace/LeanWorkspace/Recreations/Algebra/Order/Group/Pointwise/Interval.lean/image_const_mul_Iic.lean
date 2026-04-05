import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_const_mul_Iic : (fun x => a * x) '' Iic b = Iic (a * b) := by simp [mul_comm]

-- simp can prove this modulo `mul_comm`


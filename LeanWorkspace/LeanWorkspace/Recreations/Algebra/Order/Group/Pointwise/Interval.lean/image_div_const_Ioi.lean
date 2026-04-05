import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_div_const_Ioi : (fun x => x / a) '' Ioi b = Ioi (b / a) := by simp [div_eq_mul_inv]


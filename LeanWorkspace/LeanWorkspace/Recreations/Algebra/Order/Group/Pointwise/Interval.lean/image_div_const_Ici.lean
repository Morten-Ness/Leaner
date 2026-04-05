import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_div_const_Ici : (fun x => x / a) '' Ici b = Ici (b / a) := by simp [div_eq_mul_inv]


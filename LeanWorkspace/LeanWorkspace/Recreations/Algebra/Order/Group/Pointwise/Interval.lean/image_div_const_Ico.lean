import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_div_const_Ico : (fun x => x / a) '' Ico b c = Ico (b / a) (c / a) := by
  simp [div_eq_mul_inv]


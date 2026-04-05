import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_div_const_Icc : (fun x => x / a) '' Icc b c = Icc (b / a) (c / a) := by
  simp [div_eq_mul_inv]


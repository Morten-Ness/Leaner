import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_div_const_Ioc : (fun x => x / a) '' Ioc b c = Ioc (b / a) (c / a) := by
  simp [div_eq_mul_inv]


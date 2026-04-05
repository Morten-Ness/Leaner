import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_mul_const_Ioc : (fun x => x * a) ⁻¹' Ioc b c = Ioc (b / a) (c / a) := by
  simp [← Ioi_inter_Iic]


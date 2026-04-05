import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_const_mul_Ioc : (fun x => a * x) ⁻¹' Ioc b c = Ioc (b / a) (c / a) := by
  simp [← Ioi_inter_Iic]


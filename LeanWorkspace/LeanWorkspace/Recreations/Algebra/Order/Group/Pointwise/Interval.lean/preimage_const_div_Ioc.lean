import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_const_div_Ioc : (fun x => a / x) ⁻¹' Ioc b c = Ico (a / c) (a / b) := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]


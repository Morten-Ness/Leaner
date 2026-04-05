import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_const_div_Ioo : (fun x => a / x) ⁻¹' Ioo b c = Ioo (a / c) (a / b) := by
  simp [← Ioi_inter_Iio, inter_comm]


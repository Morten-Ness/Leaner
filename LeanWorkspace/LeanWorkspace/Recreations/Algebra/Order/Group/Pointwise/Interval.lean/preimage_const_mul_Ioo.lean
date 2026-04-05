import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_const_mul_Ioo : (fun x => a * x) ⁻¹' Ioo b c = Ioo (b / a) (c / a) := by
  simp [← Ioi_inter_Iio]


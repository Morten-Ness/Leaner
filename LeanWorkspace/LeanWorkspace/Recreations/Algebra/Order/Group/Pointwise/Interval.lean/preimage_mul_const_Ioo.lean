import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_mul_const_Ioo : (fun x => x * a) ⁻¹' Ioo b c = Ioo (b / a) (c / a) := by
  simp [← Ioi_inter_Iio]


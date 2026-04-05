import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_mul_const_Ico : (fun x => x * a) ⁻¹' Ico b c = Ico (b / a) (c / a) := by
  simp [← Ici_inter_Iio]


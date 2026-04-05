import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_const_mul_Icc : (fun x => a * x) ⁻¹' Icc b c = Icc (b / a) (c / a) := by
  simp [← Ici_inter_Iic]


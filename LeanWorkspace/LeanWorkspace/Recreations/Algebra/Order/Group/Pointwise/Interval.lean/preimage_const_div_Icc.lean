import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_const_div_Icc : (fun x => a / x) ⁻¹' Icc b c = Icc (a / c) (a / b) := by
  simp [← Ici_inter_Iic, inter_comm]


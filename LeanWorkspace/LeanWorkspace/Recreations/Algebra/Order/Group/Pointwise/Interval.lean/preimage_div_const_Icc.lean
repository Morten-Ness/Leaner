import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_div_const_Icc : (fun x => x / a) ⁻¹' Icc b c = Icc (b * a) (c * a) := by
  simp [div_eq_mul_inv]


import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_div_const_Iio : (fun x => x / a) ⁻¹' Iio b = Iio (b * a) := by
  simp [div_eq_mul_inv]


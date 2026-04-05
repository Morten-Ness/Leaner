import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_const_mul_Iio : (fun x => a * x) ⁻¹' Iio b = Iio (b / a) := ext fun _x => lt_div_iff_mul_lt'.symm


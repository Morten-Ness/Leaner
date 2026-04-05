import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_mul_const_Iio : (fun x => x * a) ⁻¹' Iio b = Iio (b / a) := ext fun _x => lt_div_iff_mul_lt.symm


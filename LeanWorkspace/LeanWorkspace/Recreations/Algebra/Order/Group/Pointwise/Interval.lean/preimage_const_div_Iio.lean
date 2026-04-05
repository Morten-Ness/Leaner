import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_const_div_Iio : (fun x => a / x) ⁻¹' Iio b = Ioi (a / b) := ext fun _x => div_lt_comm


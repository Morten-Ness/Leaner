import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_const_div_Ioi : (fun x => a / x) ⁻¹' Ioi b = Iio (a / b) := ext fun _x => lt_div_comm


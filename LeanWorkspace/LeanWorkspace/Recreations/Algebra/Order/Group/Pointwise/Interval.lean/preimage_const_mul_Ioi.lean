import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_const_mul_Ioi : (fun x => a * x) ⁻¹' Ioi b = Ioi (b / a) := ext fun _x => div_lt_iff_lt_mul'.symm


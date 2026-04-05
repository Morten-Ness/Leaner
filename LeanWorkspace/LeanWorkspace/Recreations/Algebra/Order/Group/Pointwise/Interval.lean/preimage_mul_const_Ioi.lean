import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_mul_const_Ioi : (fun x => x * a) ⁻¹' Ioi b = Ioi (b / a) := ext fun _x => div_lt_iff_lt_mul.symm


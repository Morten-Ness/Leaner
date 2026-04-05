import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_mul_const_Iic : (fun x => x * a) ⁻¹' Iic b = Iic (b / a) := ext fun _x => le_div_iff_mul_le.symm


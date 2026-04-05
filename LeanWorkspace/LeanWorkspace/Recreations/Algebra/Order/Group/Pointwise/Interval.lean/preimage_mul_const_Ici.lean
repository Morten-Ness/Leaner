import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_mul_const_Ici : (fun x => x * a) ⁻¹' Ici b = Ici (b / a) := ext fun _x => div_le_iff_le_mul.symm


import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_const_div_Iic : (fun x => a / x) ⁻¹' Iic b = Ici (a / b) := ext fun _x => div_le_comm


import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem preimage_const_div_Ici : (fun x => a / x) ⁻¹' Ici b = Iic (a / b) := ext fun _x => le_div_comm


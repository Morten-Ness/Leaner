import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]

variable (s t : NonemptyInterval α) (a : α)

theorem coe_inv_interval : (↑(s⁻¹) : Interval α) = (↑s)⁻¹ := rfl


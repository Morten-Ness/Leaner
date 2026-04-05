import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]

variable (s t : NonemptyInterval α) (a : α)

theorem fst_inv : s⁻¹.fst = s.snd⁻¹ := rfl


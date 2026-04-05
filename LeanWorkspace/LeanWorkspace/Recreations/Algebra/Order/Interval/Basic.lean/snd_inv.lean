import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α]

variable (s t : NonemptyInterval α) (a : α)

theorem snd_inv : s⁻¹.snd = s.fst⁻¹ := rfl


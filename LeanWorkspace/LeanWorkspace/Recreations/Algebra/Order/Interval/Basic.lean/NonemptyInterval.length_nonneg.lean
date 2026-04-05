import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

variable (s t : NonemptyInterval α) (a : α)

theorem length_nonneg : 0 ≤ s.length := sub_nonneg_of_le s.fst_le_snd


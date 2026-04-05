import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

variable (s t : NonemptyInterval α) (a : α)

omit [IsOrderedAddMonoid α] in
theorem length_zero : (0 : NonemptyInterval α).length = 0 := NonemptyInterval.length_pure _


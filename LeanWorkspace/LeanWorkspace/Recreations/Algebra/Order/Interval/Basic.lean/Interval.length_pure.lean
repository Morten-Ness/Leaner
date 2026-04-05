import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

variable (s t : Interval α) (a : α)

omit [IsOrderedAddMonoid α] in
theorem length_pure : (pure a).length = 0 := NonemptyInterval.length_pure _


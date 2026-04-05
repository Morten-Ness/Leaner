import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

variable (s t : Interval α) (a : α)

omit [IsOrderedAddMonoid α] in
theorem length_zero : (0 : Interval α).length = 0 := Interval.length_pure _


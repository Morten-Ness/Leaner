import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

variable (s t : Interval α) (a : α)

theorem length_sub_le : (s - t).length ≤ s.length + t.length := by
  simpa [sub_eq_add_neg] using Interval.length_add_le s (-t)


import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

variable (s t : NonemptyInterval α) (a : α)

theorem length_sub : (s - t).length = s.length + t.length := by simp [sub_eq_add_neg]


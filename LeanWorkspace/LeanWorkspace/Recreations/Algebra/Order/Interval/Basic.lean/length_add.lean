import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

variable (s t : NonemptyInterval α) (a : α)

theorem length_add : (s + t).length = s.length + t.length := add_sub_add_comm _ _ _ _


import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

variable (s t : Interval α) (a : α)

omit [IsOrderedAddMonoid α] in
theorem length_bot : (⊥ : Interval α).length = 0 := rfl


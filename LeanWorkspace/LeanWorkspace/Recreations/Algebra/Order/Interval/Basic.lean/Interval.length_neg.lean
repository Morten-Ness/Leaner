import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

variable (s t : Interval α) (a : α)

theorem length_neg : ∀ s : Interval α, (-s).length = s.length
  | ⊥ => rfl
  | (s : NonemptyInterval α) => NonemptyInterval.length_neg s

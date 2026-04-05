import Mathlib

open scoped Pointwise

variable {ι α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α]

variable (s t : Interval α) (a : α)

theorem length_nonneg : ∀ s : Interval α, 0 ≤ s.length
  | ⊥ => le_rfl
  | (s : NonemptyInterval α) => NonemptyInterval.length_nonneg s

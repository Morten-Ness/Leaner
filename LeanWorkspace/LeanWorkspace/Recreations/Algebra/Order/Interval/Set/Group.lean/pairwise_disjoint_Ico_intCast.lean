import Mathlib

open scoped Function -- required for scoped `on` notation

variable {α : Type*}

variable [Ring α] [PartialOrder α] [IsOrderedRing α] (a : α)

theorem pairwise_disjoint_Ico_intCast :
    Pairwise (Disjoint on fun n : ℤ => Ico (n : α) (n + 1)) := by
  simpa only [zero_add] using Set.pairwise_disjoint_Ico_add_intCast (0 : α)


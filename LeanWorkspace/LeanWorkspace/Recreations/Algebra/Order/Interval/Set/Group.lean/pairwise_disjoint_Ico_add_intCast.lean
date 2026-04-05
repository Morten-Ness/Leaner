import Mathlib

open scoped Function -- required for scoped `on` notation

variable {α : Type*}

variable [Ring α] [PartialOrder α] [IsOrderedRing α] (a : α)

theorem pairwise_disjoint_Ico_add_intCast :
    Pairwise (Disjoint on fun n : ℤ => Ico (a + n) (a + n + 1)) := by
  simpa only [zsmul_one, Int.cast_add, Int.cast_one, ← add_assoc] using
    pairwise_disjoint_Ico_add_zsmul a (1 : α)


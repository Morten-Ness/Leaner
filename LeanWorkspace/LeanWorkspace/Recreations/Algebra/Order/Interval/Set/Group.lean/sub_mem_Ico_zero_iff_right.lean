import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem sub_mem_Ico_zero_iff_right : b - a ∈ Ico 0 b ↔ a ∈ Ioc 0 b := by
  simp only [Set.sub_mem_Ico_iff_right, sub_self, sub_zero]


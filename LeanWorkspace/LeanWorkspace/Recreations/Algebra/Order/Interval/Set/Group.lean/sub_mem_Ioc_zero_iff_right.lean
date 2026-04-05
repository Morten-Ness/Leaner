import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem sub_mem_Ioc_zero_iff_right : b - a ∈ Ioc 0 b ↔ a ∈ Ico 0 b := by
  simp only [Set.sub_mem_Ioc_iff_right, sub_self, sub_zero]


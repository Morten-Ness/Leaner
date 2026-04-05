import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem sub_mem_Icc_zero_iff_right : b - a ∈ Icc 0 b ↔ a ∈ Icc 0 b := by
  simp only [Set.sub_mem_Icc_iff_right, sub_self, sub_zero]


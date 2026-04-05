import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem sub_mem_Ioo_zero_iff_right : b - a ∈ Ioo 0 b ↔ a ∈ Ioo 0 b := by
  simp only [Set.sub_mem_Ioo_iff_right, sub_self, sub_zero]


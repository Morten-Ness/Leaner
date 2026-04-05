import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem sub_mem_Ico_iff_left : a - b ∈ Set.Ico c d ↔ a ∈ Set.Ico (c + b) (d + b) := and_congr le_sub_iff_add_le sub_lt_iff_lt_add


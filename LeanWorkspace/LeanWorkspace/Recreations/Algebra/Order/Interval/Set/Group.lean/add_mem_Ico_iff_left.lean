import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem add_mem_Ico_iff_left : a + b ∈ Set.Ico c d ↔ a ∈ Set.Ico (c - b) (d - b) := (and_congr sub_le_iff_le_add lt_sub_iff_add_lt).symm


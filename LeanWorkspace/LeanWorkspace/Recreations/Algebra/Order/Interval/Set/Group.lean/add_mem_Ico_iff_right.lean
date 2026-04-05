import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem add_mem_Ico_iff_right : a + b ∈ Set.Ico c d ↔ b ∈ Set.Ico (c - a) (d - a) := (and_congr sub_le_iff_le_add' lt_sub_iff_add_lt').symm


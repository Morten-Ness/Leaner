import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem add_mem_Icc_iff_left : a + b ∈ Set.Icc c d ↔ a ∈ Set.Icc (c - b) (d - b) := (and_congr sub_le_iff_le_add le_sub_iff_add_le).symm


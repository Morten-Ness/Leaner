import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem add_mem_Ioo_iff_left : a + b ∈ Set.Ioo c d ↔ a ∈ Set.Ioo (c - b) (d - b) := (and_congr sub_lt_iff_lt_add lt_sub_iff_add_lt).symm


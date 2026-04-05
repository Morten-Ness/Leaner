import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem add_mem_Icc_iff_right : a + b ∈ Set.Icc c d ↔ b ∈ Set.Icc (c - a) (d - a) := (and_congr sub_le_iff_le_add' le_sub_iff_add_le').symm


import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem add_mem_Ioc_iff_right : a + b ∈ Set.Ioc c d ↔ b ∈ Set.Ioc (c - a) (d - a) := (and_congr sub_lt_iff_lt_add' le_sub_iff_add_le').symm


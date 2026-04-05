import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem sub_mem_Ioc_iff_right : a - b ∈ Set.Ioc c d ↔ b ∈ Set.Ico (a - d) (a - c) := and_comm.trans <| and_congr sub_le_comm lt_sub_comm


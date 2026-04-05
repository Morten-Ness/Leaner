import Mathlib

variable {α : Type*}

variable [AddCommGroup α] [PartialOrder α] [IsOrderedAddMonoid α] {a b c d : α}

theorem sub_mem_Ioo_iff_right : a - b ∈ Set.Ioo c d ↔ b ∈ Set.Ioo (a - d) (a - c) := and_comm.trans <| and_congr sub_lt_comm lt_sub_comm

-- I think that symmetric intervals deserve attention and API: they arise all the time,
-- for instance when considering metric balls in `ℝ`.


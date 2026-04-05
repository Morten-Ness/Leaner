import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {a c d : α}

theorem inv_mem_Ioo_iff : a⁻¹ ∈ Set.Ioo c d ↔ a ∈ Set.Ioo d⁻¹ c⁻¹ := and_comm.trans <| and_congr inv_lt' lt_inv'


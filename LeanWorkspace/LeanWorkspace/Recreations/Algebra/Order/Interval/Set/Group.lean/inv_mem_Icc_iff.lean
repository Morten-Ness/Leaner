import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {a c d : α}

theorem inv_mem_Icc_iff : a⁻¹ ∈ Set.Icc c d ↔ a ∈ Set.Icc d⁻¹ c⁻¹ := and_comm.trans <| and_congr inv_le' le_inv'


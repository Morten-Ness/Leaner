import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {a c d : α}

theorem inv_mem_Ioc_iff : a⁻¹ ∈ Set.Ioc c d ↔ a ∈ Set.Ico d⁻¹ c⁻¹ := and_comm.trans <| and_congr inv_le' lt_inv'


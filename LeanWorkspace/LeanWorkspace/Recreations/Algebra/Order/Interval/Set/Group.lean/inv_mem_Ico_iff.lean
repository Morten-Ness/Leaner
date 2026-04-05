import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] {a c d : α}

theorem inv_mem_Ico_iff : a⁻¹ ∈ Set.Ico c d ↔ a ∈ Set.Ioc d⁻¹ c⁻¹ := and_comm.trans <| and_congr inv_lt' le_inv'


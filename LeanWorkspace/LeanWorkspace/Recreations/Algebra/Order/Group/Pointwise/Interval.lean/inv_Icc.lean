import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem inv_Icc (a b : α) : (Icc a b)⁻¹ = Icc b⁻¹ a⁻¹ := by simp [← Ici_inter_Iic, inter_comm]


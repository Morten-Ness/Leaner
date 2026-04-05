import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem inv_Ioo (a b : α) : (Ioo a b)⁻¹ = Ioo b⁻¹ a⁻¹ := by simp [← Ioi_inter_Iio, inter_comm]


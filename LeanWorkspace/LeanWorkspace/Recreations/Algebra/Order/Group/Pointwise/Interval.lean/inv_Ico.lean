import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem inv_Ico (a b : α) : (Ico a b)⁻¹ = Ioc b⁻¹ a⁻¹ := by
  simp [← Ici_inter_Iio, ← Ioi_inter_Iic, inter_comm]


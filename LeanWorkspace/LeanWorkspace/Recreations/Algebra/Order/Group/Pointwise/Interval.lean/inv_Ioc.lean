import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem inv_Ioc (a b : α) : (Ioc a b)⁻¹ = Ico b⁻¹ a⁻¹ := by
  simp [← Ioi_inter_Iic, ← Ici_inter_Iio, inter_comm]


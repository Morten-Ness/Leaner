import Mathlib

variable {α : Type*}

variable [CommGroup α] [PartialOrder α] [IsOrderedMonoid α] (a b c : α)

theorem image_const_mul_Iio : (fun x => a * x) '' Iio b = Iio (a * b) := by simp [mul_comm]


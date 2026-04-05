import Mathlib

variable {α : Type*} [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

theorem min_div_div_right' (a b c : α) : min (a / c) (b / c) = min a b / c := by
  simpa only [div_eq_mul_inv] using min_mul_mul_right a b c⁻¹


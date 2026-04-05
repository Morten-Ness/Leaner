import Mathlib

variable {α : Type*} [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

theorem max_div_div_right' (a b c : α) : max (a / c) (b / c) = max a b / c := by
  simpa only [div_eq_mul_inv] using max_mul_mul_right a b c⁻¹


import Mathlib

variable {α : Type*} [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

theorem min_div_div_left' (a b c : α) : min (a / b) (a / c) = a / max b c := by
  simp only [div_eq_mul_inv, min_mul_mul_left, min_inv_inv']


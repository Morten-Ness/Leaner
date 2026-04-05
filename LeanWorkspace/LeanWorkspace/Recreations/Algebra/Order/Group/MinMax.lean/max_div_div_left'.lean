import Mathlib

variable {α : Type*} [CommGroup α] [LinearOrder α] [IsOrderedMonoid α]

theorem max_div_div_left' (a b c : α) : max (a / b) (a / c) = a / min b c := by
  simp only [div_eq_mul_inv, max_mul_mul_left, max_inv_inv']


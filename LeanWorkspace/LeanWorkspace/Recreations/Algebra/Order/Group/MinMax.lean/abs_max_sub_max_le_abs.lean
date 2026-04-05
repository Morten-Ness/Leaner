import Mathlib

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

theorem abs_max_sub_max_le_abs (a b c : α) : |max a c - max b c| ≤ |a - b| := by
  simpa only [sub_self, abs_zero, max_eq_left (abs_nonneg (a - b))]
    using abs_max_sub_max_le_max a c b c


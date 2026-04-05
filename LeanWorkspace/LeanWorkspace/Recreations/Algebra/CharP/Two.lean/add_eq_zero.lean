import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem add_eq_zero {a b : R} : a + b = 0 ↔ a = b := by
  rw [← CharTwo.sub_eq_add, sub_eq_iff_eq_add, zero_add]


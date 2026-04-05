import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem add_eq_iff_eq_add {a b c : R} : a + b = c ↔ a = c + b := by
  rw [← sub_eq_iff_eq_add, CharTwo.sub_eq_add]


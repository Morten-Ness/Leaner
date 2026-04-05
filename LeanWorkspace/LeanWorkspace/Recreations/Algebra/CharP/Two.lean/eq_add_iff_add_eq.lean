import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem eq_add_iff_add_eq {a b c : R} : a = b + c ↔ a + c = b := by
  rw [← eq_sub_iff_add_eq, CharTwo.sub_eq_add]


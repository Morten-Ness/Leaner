import Mathlib

variable {R ι : Type*}

variable [Ring R] [CharP R 2]

theorem neg_eq (x : R) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, CharTwo.add_self_eq_zero]


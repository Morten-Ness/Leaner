import Mathlib

variable {R ι : Type*}

variable [Semiring R] [CharP R 2]

theorem add_cancel_right (a b : R) : a + b + b = a := by
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]


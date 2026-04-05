import Mathlib

variable {R ι : Type*}

variable [Semiring R] [CharP R 2]

theorem add_cancel_left (a b : R) : a + (a + b) = b := by
  rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]


import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by
  rw [h, div_eq_mul_inv, mul_comm c, mul_inv_cancel_left]


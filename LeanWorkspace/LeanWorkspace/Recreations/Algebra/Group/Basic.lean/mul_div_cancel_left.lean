import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_div_cancel_left (a b : G) : a * b / a = b := by rw [div_eq_inv_mul, inv_mul_cancel_left]


import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c := by
  rw [← div_mul, mul_div_cancel_left]


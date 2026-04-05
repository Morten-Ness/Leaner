import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_div_cancel (a b : G) : a * (b / a) = b := by
  rw [← mul_div_assoc, mul_div_cancel_left]


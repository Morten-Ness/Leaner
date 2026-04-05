import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b := by
  rw [mul_assoc, mul_div_cancel]


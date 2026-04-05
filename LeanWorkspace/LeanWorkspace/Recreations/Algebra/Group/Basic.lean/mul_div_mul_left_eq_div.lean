import Mathlib

variable {α β G M : Type*}

variable [CommGroup G] {a b c d : G}

theorem mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b := by
  simp


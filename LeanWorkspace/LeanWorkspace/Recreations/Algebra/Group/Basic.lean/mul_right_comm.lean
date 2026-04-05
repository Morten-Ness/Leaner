import Mathlib

variable {α β G M : Type*}

variable [CommSemigroup G]

theorem mul_right_comm (a b c : G) : a * b * c = a * c * b := by
  rw [mul_assoc, mul_comm b, mul_assoc]


import Mathlib

variable {α β G M : Type*}

variable [CommSemigroup G]

theorem mul_left_comm (a b c : G) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a, mul_assoc]


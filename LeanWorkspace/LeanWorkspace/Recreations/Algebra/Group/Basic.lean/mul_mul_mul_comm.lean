import Mathlib

variable {α β G M : Type*}

variable [CommSemigroup G]

theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by
  simp only [mul_left_comm, mul_assoc]


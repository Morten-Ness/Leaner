import Mathlib

variable {α β G M : Type*}

variable [CommSemigroup G]

theorem mul_rotate (a b c : G) : a * b * c = b * c * a := by
  simp only [mul_left_comm, mul_comm]


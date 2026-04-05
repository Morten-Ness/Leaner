import Mathlib

variable {α : Type*}

variable [CommMonoid α] {a b : α} {u : αˣ}

theorem mul_left_dvd : ↑u * a ∣ b ↔ a ∣ b := by
  rw [mul_comm]
  apply Units.mul_right_dvd


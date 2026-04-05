import Mathlib

variable {α : Type*}

variable [CommMonoid α] {a b : α} {u : αˣ}

theorem dvd_mul_left : a ∣ u * b ↔ a ∣ b := by
  rw [mul_comm]
  apply Units.dvd_mul_right


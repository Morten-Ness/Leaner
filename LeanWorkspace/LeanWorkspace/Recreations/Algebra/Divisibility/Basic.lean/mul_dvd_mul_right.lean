import Mathlib

variable {α : Type*}

variable [CommMonoid α] {a b : α}

theorem mul_dvd_mul_right (h : a ∣ b) (c : α) : a * c ∣ b * c := by
  gcongr


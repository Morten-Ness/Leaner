import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_eq_right_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize b = b) :
    lcm a b = b ↔ a ∣ b := by simpa only [lcm_comm b a] using lcm_eq_left_iff b a h


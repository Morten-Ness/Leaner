import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_eq_right_iff [NormalizedGCDMonoid α] (a b : α) (h : normalize b = b) :
    gcd a b = b ↔ b ∣ a := by simpa only [gcd_comm a b] using gcd_eq_left_iff b a h


import Mathlib

variable {α : Type*}

variable [CommRing α] [NormalizedGCDMonoid α]

theorem gcd_eq_of_dvd_sub_left {a b c : α} (h : a ∣ b - c) : gcd b a = gcd c a := by
  rw [gcd_comm _ a, gcd_comm _ a, gcd_eq_of_dvd_sub_right h]


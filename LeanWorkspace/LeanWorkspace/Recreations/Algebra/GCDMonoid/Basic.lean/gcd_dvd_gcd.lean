import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem gcd_dvd_gcd [GCDMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : gcd a c ∣ gcd b d := dvd_gcd ((gcd_dvd_left _ _).trans hab) ((gcd_dvd_right _ _).trans hcd)


import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_dvd_lcm [GCDMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : lcm a c ∣ lcm b d := lcm_dvd (hab.trans (dvd_lcm_left _ _)) (hcd.trans (dvd_lcm_right _ _))


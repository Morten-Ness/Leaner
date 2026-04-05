import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [GCDMonoid α] {m n a b c : α}

variable {p : α} (hp : Prime p)

theorem dvd_or_dvd_of_dvd_lcm (h : p ∣ lcm a b) : p ∣ a ∨ p ∣ b := dvd_or_dvd hp (h.trans (lcm_dvd_mul a b))


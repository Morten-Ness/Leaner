import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [GCDMonoid α] {m n a b c : α}

theorem dvd_of_lcm_left_dvd (h : lcm a b ∣ c) : b ∣ c := (dvd_lcm_right a b).trans h


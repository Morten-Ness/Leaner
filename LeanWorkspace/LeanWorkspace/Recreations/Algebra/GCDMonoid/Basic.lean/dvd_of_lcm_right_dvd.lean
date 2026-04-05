import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [GCDMonoid α] {m n a b c : α}

theorem dvd_of_lcm_right_dvd (h : lcm a b ∣ c) : a ∣ c := (dvd_lcm_left a b).trans h


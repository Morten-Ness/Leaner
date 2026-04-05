import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [GCDMonoid α] {m n a b c : α}

theorem dvd_lcm_of_dvd_left (h : a ∣ b) (c : α) : a ∣ lcm b c := h.trans (dvd_lcm_left b c)

alias Dvd.dvd.lcm_right := dvd_lcm_of_dvd_left


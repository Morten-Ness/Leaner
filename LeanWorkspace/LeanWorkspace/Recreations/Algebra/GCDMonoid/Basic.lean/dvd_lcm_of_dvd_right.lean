import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable [GCDMonoid α] {m n a b c : α}

theorem dvd_lcm_of_dvd_right (h : a ∣ b) (c : α) : a ∣ lcm c b := h.trans (dvd_lcm_right c b)

alias Dvd.dvd.lcm_left := dvd_lcm_of_dvd_right


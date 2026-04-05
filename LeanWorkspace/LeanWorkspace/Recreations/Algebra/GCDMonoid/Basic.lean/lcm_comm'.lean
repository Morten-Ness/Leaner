import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_comm' [GCDMonoid α] (a b : α) : Associated (lcm a b) (lcm b a) := associated_of_dvd_dvd (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))


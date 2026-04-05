import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_one_right [NormalizedGCDMonoid α] (a : α) : lcm a 1 = normalize a := lcm_units_coe_right a 1


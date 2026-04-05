import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_one_left [NormalizedGCDMonoid α] (a : α) : lcm 1 a = normalize a := lcm_units_coe_left 1 a


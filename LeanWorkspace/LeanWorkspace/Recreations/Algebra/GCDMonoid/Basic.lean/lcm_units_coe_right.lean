import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem lcm_units_coe_right [NormalizedGCDMonoid α] (a : α) (u : αˣ) : lcm a ↑u = normalize a := (lcm_comm a u).trans <| lcm_units_coe_left _ _


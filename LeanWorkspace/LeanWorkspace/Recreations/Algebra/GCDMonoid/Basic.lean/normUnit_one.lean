import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [NormalizationMonoid α]

theorem normUnit_one : normUnit (1 : α) = 1 := normUnit_coe_units 1


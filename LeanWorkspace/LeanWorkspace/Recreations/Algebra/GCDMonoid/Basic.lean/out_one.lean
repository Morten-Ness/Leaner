import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizationMonoid α]

theorem out_one : (1 : Associates α).out = 1 := normalize_one


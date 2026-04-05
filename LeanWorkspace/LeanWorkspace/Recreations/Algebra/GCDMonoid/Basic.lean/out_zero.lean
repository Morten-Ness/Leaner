import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizationMonoid α]

theorem out_zero : (0 : Associates α).out = 0 := by
  simp


import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizationMonoid α]

theorem normalize_out (a : Associates α) : normalize a.out = a.out := Quotient.inductionOn a normalize_idem


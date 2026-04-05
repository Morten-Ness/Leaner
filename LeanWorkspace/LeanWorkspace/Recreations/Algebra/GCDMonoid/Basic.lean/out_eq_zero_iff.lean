import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizationMonoid α]

theorem out_eq_zero_iff {a : Associates α} : a.out = 0 ↔ a = 0 := Quotient.inductionOn a (by simp)


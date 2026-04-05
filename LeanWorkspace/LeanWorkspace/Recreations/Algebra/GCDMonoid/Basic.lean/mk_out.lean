import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizationMonoid α]

theorem mk_out (a : Associates α) : Associates.mk a.out = a := Quotient.inductionOn a mk_normalize


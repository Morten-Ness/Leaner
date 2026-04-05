import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizationMonoid α]

theorem out_mk (a : α) : (Associates.mk a).out = normalize a := rfl


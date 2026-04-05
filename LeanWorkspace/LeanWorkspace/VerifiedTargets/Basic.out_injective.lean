import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizationMonoid α]

theorem out_injective : Function.Injective (Associates.out : _ → α) := Function.LeftInverse.injective Associates.mk_out


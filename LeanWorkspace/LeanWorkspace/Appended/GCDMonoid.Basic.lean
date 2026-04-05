import Mathlib

section

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizationMonoid α]

theorem normalize_out (a : Associates α) : normalize a.out = a.out := Quotient.inductionOn a normalize_idem

end

section

variable {α : Type*}

variable [CommMonoidWithZero α] [IsCancelMulZero α] [NormalizationMonoid α]

theorem out_injective : Function.Injective (Associates.out : _ → α) := Function.LeftInverse.injective Associates.mk_out

end

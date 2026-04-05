import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

variable {x y : α}

theorem not_isRelPrime_zero_zero [Nontrivial α] : ¬IsRelPrime (0 : α) 0 := mt isRelPrime_zero_right.mp not_isUnit_zero


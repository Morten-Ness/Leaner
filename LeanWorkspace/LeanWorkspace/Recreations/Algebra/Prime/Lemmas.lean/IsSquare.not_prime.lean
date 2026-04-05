import Mathlib

variable {M N : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

variable {a p : M}

theorem IsSquare.not_prime (ha : IsSquare a) : ¬Prime a := fun h => h.not_isSquare ha


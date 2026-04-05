import Mathlib

variable {M N : Type*}

variable [CommMonoidWithZero M] [IsCancelMulZero M]

variable {a p : M}

theorem Prime.not_isSquare (hp : Prime p) : ¬IsSquare p := hp.irreducible.not_isSquare


import Mathlib

variable {R S : Type*}

variable (R) [NonAssocRing R]

theorem ringChar_ne_zero_of_finite [Finite R] : ringChar R ≠ 0 := CharP.char_ne_zero_of_finite R (ringChar R)


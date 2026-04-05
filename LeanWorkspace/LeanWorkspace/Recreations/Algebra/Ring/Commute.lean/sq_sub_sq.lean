import Mathlib

variable {R : Type u}

variable [CommRing R]

theorem sq_sub_sq (a b : R) : a ^ 2 - b ^ 2 = (a + b) * (a - b) := (Commute.all a b).sq_sub_sq

alias pow_two_sub_pow_two := sq_sub_sq


import Mathlib

variable {R S G M N O ι : Type*}

variable [Ring R]

theorem single_neg (m : M) (r : R) : single m (-r) = -single m r := Finsupp.single_neg m r


import Mathlib

variable {ι F R S T M N O : Type*}

variable [Ring R] [Ring S]

theorem map_neg (f : R →+ S) (x : R[M]) : MonoidAlgebra.map f (-x) = -MonoidAlgebra.map f x := Finsupp.mapRange_neg (hf := f.map_zero) f.map_neg ..


import Mathlib

variable {ι F R S T M N O : Type*}

variable [Ring R] [Ring S]

theorem map_sub (f : R →+ S) (x y : R[M]) : MonoidAlgebra.map f (x - y) = MonoidAlgebra.map f x - MonoidAlgebra.map f y := Finsupp.mapRange_sub (hf := f.map_zero) f.map_sub ..


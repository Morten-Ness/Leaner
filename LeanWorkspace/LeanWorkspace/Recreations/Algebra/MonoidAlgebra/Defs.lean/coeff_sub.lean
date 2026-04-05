import Mathlib

variable {R S G M N O ι : Type*}

variable [Ring R]

theorem coeff_sub (x y : R[M]) : MonoidAlgebra.coeff (x - y) = MonoidAlgebra.coeff x - MonoidAlgebra.coeff y := rfl


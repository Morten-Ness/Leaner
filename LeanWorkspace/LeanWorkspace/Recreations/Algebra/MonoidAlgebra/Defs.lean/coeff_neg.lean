import Mathlib

variable {R S G M N O ι : Type*}

variable [Ring R]

theorem coeff_neg (x : R[M]) : MonoidAlgebra.coeff (-x) = -MonoidAlgebra.coeff x := rfl


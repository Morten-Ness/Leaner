import Mathlib

variable {R S G M N O ι : Type*}

variable [Ring R]

theorem ofCoeff_sub (x y : M →₀ R) : MonoidAlgebra.ofCoeff (x - y) = MonoidAlgebra.ofCoeff x - MonoidAlgebra.ofCoeff y := rfl


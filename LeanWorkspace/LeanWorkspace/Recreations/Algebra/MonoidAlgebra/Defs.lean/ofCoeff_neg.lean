import Mathlib

variable {R S G M N O ι : Type*}

variable [Ring R]

theorem ofCoeff_neg (x : M →₀ R) : MonoidAlgebra.ofCoeff (-x) = -MonoidAlgebra.ofCoeff x := rfl


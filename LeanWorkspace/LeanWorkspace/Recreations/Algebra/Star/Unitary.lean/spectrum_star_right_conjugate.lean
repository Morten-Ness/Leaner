import Mathlib

variable {R : Type*}

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] [StarMul A]

theorem spectrum_star_right_conjugate {a : A} {U : unitary A} :
    spectrum R (U * a * (star U : A)) = spectrum R a := spectrum.units_conjugate (u := Unitary.toUnits U)


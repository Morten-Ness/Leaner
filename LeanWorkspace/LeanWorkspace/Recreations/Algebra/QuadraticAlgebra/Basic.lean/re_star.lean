import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem re_star (z : QuadraticAlgebra R a b) :
    (star z).re = z.re + b * z.im := rfl


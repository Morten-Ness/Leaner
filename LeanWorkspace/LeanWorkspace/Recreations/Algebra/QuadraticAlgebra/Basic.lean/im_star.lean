import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem im_star (z : QuadraticAlgebra R a b) :
    (star z).im = -z.im := rfl


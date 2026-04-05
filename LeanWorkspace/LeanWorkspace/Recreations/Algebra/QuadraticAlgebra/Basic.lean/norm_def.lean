import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem norm_def (z : QuadraticAlgebra R a b) :
    z.norm = z.re * z.re + b * z.re * z.im - a * z.im * z.im := rfl


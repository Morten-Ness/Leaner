import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem star_mk (x y : R) :
    star (⟨x, y⟩ : QuadraticAlgebra R a b) = ⟨x + b * y, -y⟩ := rfl


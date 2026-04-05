import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [CommSemiring R]

theorem algebraMap_inj {x y : R} :
    algebraMap R (QuadraticAlgebra R a b) x = algebraMap _ _ y ↔ x = y := QuadraticAlgebra.algebraMap_injective.eq_iff


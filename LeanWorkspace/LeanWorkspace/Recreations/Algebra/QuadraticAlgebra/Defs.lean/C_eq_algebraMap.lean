import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [CommSemiring R]

theorem C_eq_algebraMap : QuadraticAlgebra.C = (algebraMap R (QuadraticAlgebra R a b)) := rfl

